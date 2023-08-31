#![allow(incomplete_features)]
#![feature(
    more_qualified_paths,
    iter_next_chunk,
    generic_const_exprs,
    iter_array_chunks
)]
#![no_std]

#[cfg(feature = "non_fixed")]
extern crate alloc;

use core::fmt::Debug;

#[cfg(feature = "non_fixed")]
use alloc::vec::Vec;

#[derive(Debug)]
/// A generic error encountered while parsing.
pub enum ParserError {
    /// The parser expected more data than it got.
    TooLittleData(usize),
    /// Just like TooLittleData, but more specific.
    HeaderIncomplete(usize),
    /// The expected magic was invalid.
    InvalidMagic,
    /// A value wasn't understood by the parser.
    ValueNotUnderstood,
    /// While parsing an array, the parser errored earlier than expected.
    ArrayTooShort,
}

/// Relevant for parsing numbers.
#[derive(Debug, Copy, Clone)]
pub enum Endian {
    Little,
    Big,
}
/// A trait indicating, that a type only has one fixed size.
pub trait StaticallySized {
    const SIZE: usize;
}
#[cfg(feature = "non_fixed")]
/// A trait for reading a non fixed amount of data.
pub trait Read
where
    Self: Sized,
{
    fn from_bytes(data: &mut impl ExactSizeIterator<Item = u8>) -> Result<Self, ParserError>;
}
#[cfg(feature = "non_fixed")]
/// A trait for reading a non fixed amount of data, with context.
pub trait ReadCtx<Ctx>
where
    Self: Sized,
{
    fn from_bytes(
        data: &mut impl ExactSizeIterator<Item = u8>,
        ctx: Ctx,
    ) -> Result<Self, ParserError>;
}
#[cfg(feature = "non_fixed")]
/// A trait for writing data of variable length.
pub trait Write {
    fn to_bytes(&self) -> Vec<u8>;
}
#[cfg(feature = "non_fixed")]
/// A trait for writing data of variable length, with context.
pub trait WriteCtx<Ctx> {
    fn to_bytes(&self, ctx: Ctx) -> Vec<u8>;
}
/// A trait for reading data of fixed length.
pub trait ReadFixed<const N: usize>
where
    Self: Sized,
{
    fn from_bytes(data: &[u8; N]) -> Result<Self, ParserError>;
}
/// A trait for reading data of fixed length, with context.
pub trait ReadFixedCtx<const N: usize, Ctx>
where
    Self: Sized,
{
    fn from_bytes(data: &[u8; N], ctx: Ctx) -> Result<Self, ParserError>;
}
/// A trait for writing data of fixed length.
pub trait WriteFixed<const N: usize>
where
    Self: Sized,
{
    fn to_bytes(&self) -> [u8; N];
}
/// A trait for writing data of fixed length, with context.
pub trait WriteFixedCtx<const N: usize, Ctx>
where
    Self: Sized,
{
    fn to_bytes(&self, ctx: Ctx) -> [u8; N];
}
#[cfg(feature = "non_fixed")]
impl<T> Read for Vec<T>
where
    T: Read,
{
    fn from_bytes(data: &mut impl ExactSizeIterator<Item = u8>) -> Result<Self, ParserError> {
        Ok((0..).map_while(|_| T::from_bytes(data).ok()).collect()) // Create an infinte iterator, map until from_bytes returns an Error and collect.
    }
}

#[cfg(feature = "non_fixed")]
impl<T, Ctx> ReadCtx<Ctx> for Vec<T>
where
    T: ReadCtx<Ctx>,
    Ctx: Clone,
{
    fn from_bytes(
        data: &mut impl ExactSizeIterator<Item = u8>,
        ctx: Ctx,
    ) -> Result<Self, ParserError> {
        Ok((0..)
            .map_while(|_| T::from_bytes(data, ctx.clone()).ok())
            .collect()) // Create an infinte iterator, map until from_bytes returns an Error and collect.
    }
}
#[cfg(feature = "non_fixed")]
impl<'a, T> Write for Vec<T>
where
    T: Write,
{
    fn to_bytes(&self) -> Vec<u8> {
        self.iter().flat_map(T::to_bytes).collect()
    }
}
#[cfg(feature = "non_fixed")]
impl<'a, T, Ctx> WriteCtx<Ctx> for Vec<T>
where
    T: WriteCtx<Ctx>,
    Ctx: Clone,
{
    fn to_bytes(&self, ctx: Ctx) -> Vec<u8> {
        self.iter().flat_map(|x| x.to_bytes(ctx.clone())).collect()
    }
}
impl<const N: usize, T> ReadFixed<{ T::SIZE * N }> for [T; N]
where
    T: StaticallySized + ReadFixed<{ T::SIZE }> + Default + Copy,
    [(); T::SIZE * N]:,
{
    fn from_bytes(data: &[u8; T::SIZE * N]) -> Result<Self, ParserError> {
        let mut output = [T::default(); N];
        for (i, x) in data
            .iter()
            .copied()
            .array_chunks::<{ T::SIZE }>()
            .map(|x| T::from_bytes(&x))
            .enumerate()
        {
            output[i] = x?;
        }
        Ok(output)
    }
}
impl<const N: usize, T> WriteFixed<{ T::SIZE * N }> for [T; N]
where
    T: StaticallySized + WriteFixed<{ T::SIZE }> + Default + Copy,
    [(); T::SIZE * N]:,
{
    fn to_bytes(&self) -> [u8; T::SIZE * N] {
        self.into_iter().flat_map(T::to_bytes).next_chunk().unwrap()
    }
}
#[cfg(feature = "non_fixed")]
impl<const N: usize, T: Read + Default + Copy> Read for [T; N] {
    fn from_bytes(data: &mut impl ExactSizeIterator<Item = u8>) -> Result<Self, ParserError> {
        (0..N)
            .map_while(|_| T::from_bytes(data).ok())
            .next_chunk()
            .map_err(|_| ParserError::ArrayTooShort)
    }
}
#[cfg(feature = "non_fixed")]
impl<'a, const N: usize, T: Write> Write for [T; N] {
    fn to_bytes(&self) -> Vec<u8> {
        self.into_iter().flat_map(T::to_bytes).collect()
    }
}
#[macro_export]
/// This macro allows turning enums into numbers and vice versa.
/// ```
/// #![feature(more_qualified_paths)]
///
/// #[derive(Debug, PartialEq)]
/// enum ABC {
///     A,
///     B,
///     C,
///     Unknown(u8),
/// }
/// bin_utils::enum_to_int! {
///     u8,
///     ABC,
///
///     0x01,
///     ABC::A,
///     0x02,
///     ABC::B,
///     0x03,
///     ABC::C
/// }
///
/// let a: ABC = 0x01.into();
/// assert_eq!(a, ABC::A);
/// let a: u8 = a.into();
/// assert_eq!(a, 0x01);
/// let unknown: ABC = 0xff.into();
/// assert_eq!(unknown, ABC::Unknown(0xff));
/// ```
macro_rules! enum_to_int {
    ($a:ty, $b:ty, $($x:expr, $y:path), +) => {
        impl From<$a> for $b {
            fn from(value: $a) -> Self {
                match value {
                    $($x => $y,)+
                    _ => Self::Unknown(value),
                }
            }
        }
        impl From<$b> for $a {
            fn from(value: $b) -> Self {
                match value {
                    $($y => $x,)+
                    <$b>::Unknown(value) => value
                }
            }
        }
    }
}

#[cfg(feature = "numeric_rw")]
mod numeric_rw {
    use super::*;
    macro_rules! impl_rw_numeric {
        ($number_type:ty) => {
            impl StaticallySized for $number_type {
                const SIZE: usize = { ::core::mem::size_of::<$number_type>() };
            }
            impl ReadFixedCtx<{ ::core::mem::size_of::<$number_type>() }, &Endian> for $number_type {
                fn from_bytes(
                    data: &[u8; { ::core::mem::size_of::<$number_type>() }],
                    ctx: &Endian,
                ) -> Result<Self, ParserError> {
                    let function = match *ctx {
                        Endian::Little => <$number_type>::from_le_bytes,
                        Endian::Big => <$number_type>::from_be_bytes,
                    };
                    Ok(function(*data))
                }
            }
            #[cfg(feature = "non_fixed")]
            impl ReadCtx<&Endian> for $number_type {
                fn from_bytes(
                    data: &mut impl ExactSizeIterator<Item = u8>,
                    ctx: &Endian,
                ) -> Result<Self, ParserError> {
                    let mut iter =
                        ::try_take::try_take(data, { ::core::mem::size_of::<$number_type>() })
                            .map_err(ParserError::TooLittleData)?;
                    <$number_type as ReadFixedCtx<
                        { ::core::mem::size_of::<$number_type>() },
                        &Endian,
                    >>::from_bytes(&iter.next_chunk().unwrap(), ctx)
                }
            }
            impl WriteFixedCtx<{ ::core::mem::size_of::<$number_type>() }, &Endian>
                for $number_type
            {
                fn to_bytes(
                    &self,
                    ctx: &Endian,
                ) -> [u8; { ::core::mem::size_of::<$number_type>() }] {
                    let function = match *ctx {
                        Endian::Little => <$number_type>::to_le_bytes,
                        Endian::Big => <$number_type>::to_be_bytes,
                    };
                    function(*self)
                }
            }
            #[cfg(feature = "non_fixed")]
            impl<'a> WriteCtx<&Endian> for $number_type {
                fn to_bytes(&self, ctx: &Endian) -> ::alloc::vec::Vec<u8> {
                    <Self as WriteFixedCtx<{ ::core::mem::size_of::<$number_type>() }, &Endian>>::to_bytes(self, ctx).to_vec()
                }
            }
        };
    }
    impl_rw_numeric!(u8);
    impl_rw_numeric!(i8);
    impl_rw_numeric!(u16);
    impl_rw_numeric!(i16);
    impl_rw_numeric!(u32);
    impl_rw_numeric!(i32);
    impl_rw_numeric!(u64);
    impl_rw_numeric!(i64);
    impl_rw_numeric!(u128);
    impl_rw_numeric!(i128);
}
#[cfg(feature = "numeric_rw")]
pub use numeric_rw::*;
