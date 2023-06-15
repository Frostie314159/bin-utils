#![feature(more_qualified_paths)]
#![feature(iter_next_chunk)]
#![no_std]

#[cfg(feature = "non_fixed")]
extern crate alloc;

use core::fmt::Debug;

#[cfg(feature = "non_fixed")]
use alloc::borrow::Cow;

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
}

/// Relevant for parsing numbers.
pub enum Endian {
    Little,
    Big,
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
pub trait Write<'a> {
    fn to_bytes(&self) -> Cow<'a, [u8]>;
}
#[cfg(feature = "non_fixed")]
/// A trait for writing data of variable length, with context.
pub trait WriteCtx<'a, Ctx> {
    fn to_bytes(&self, ctx: Ctx) -> Cow<'a, [u8]>;
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
    use alloc::borrow::ToOwned;
    impl Read for u8 {
        fn from_bytes(data: &mut impl ExactSizeIterator<Item = u8>) -> Result<Self, ParserError> {
            data.next().ok_or(ParserError::TooLittleData(1))
        }
    }
    impl Read for i8 {
        fn from_bytes(data: &mut impl ExactSizeIterator<Item = u8>) -> Result<Self, ParserError> {
            data.next().ok_or(ParserError::TooLittleData(1)).map(|x| x as i8)
        }
    }
    impl<'a> Write<'a> for u8 {
        fn to_bytes(&self) -> Cow<'a, [u8]> {
            Cow::Owned([*self].as_slice().to_owned())
        }
    }impl<'a> Write<'a> for i8 {
        fn to_bytes(&self) -> Cow<'a, [u8]> {
            Cow::Owned([*self as u8].as_slice().to_owned())
        }
    }
    macro_rules! impl_rw_numeric {
        ($number_type:ty) => {
            impl ReadCtx<Endian> for $number_type {
                fn from_bytes(
                    data: &mut impl ExactSizeIterator<Item = u8>,
                    ctx: Endian,
                ) -> Result<Self, ParserError> {
                    Ok(match ctx {
                        Endian::Little => <$number_type>::from_le_bytes(
                            data.next_chunk()
                                .map_err(|x| ParserError::TooLittleData(core::mem::size_of::<$number_type>() - x.len()))?,
                        ),
                        Endian::Big => <$number_type>::from_be_bytes(
                            data.next_chunk()
                                .map_err(|x| ParserError::TooLittleData(core::mem::size_of::<$number_type>() - x.len()))?,
                        ),
                    })
                }
            }
            impl<'a> WriteCtx<'a, Endian> for $number_type {
                fn to_bytes(&self, ctx: Endian) -> Cow<'a, [u8]> {
                    match ctx {
                        Endian::Little => self.to_le_bytes(),
                        Endian::Big => self.to_be_bytes()
                    }.as_slice().to_owned().into()
                }
            }
        };
    }
    impl_rw_numeric!(u16);
    impl_rw_numeric!(i16);
    impl_rw_numeric!(u32);
    impl_rw_numeric!(i32);
    impl_rw_numeric!(u64);
    impl_rw_numeric!(i64);
    impl_rw_numeric!(u128);
    impl_rw_numeric!(i128);
}
pub use numeric_rw::*;