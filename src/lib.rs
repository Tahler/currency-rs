// TODO issues with precision. truncation all over the place

// Copyright (c) 2016 Tyler Berry All Rights Reserved.
//
// Licensed under the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>.
// This file may not be copied, modified, or distributed except according to those terms.

//! A `Currency` is a combination of an optional character (`Option<char>``) and a big integer
//! (`BigInt`).
//!
//! Common operations are overloaded to make numerical operations easy.
//!
//! Perhaps the most useful part of this crate is the `Currency::from_str` function, which can
//! convert international currency representations such as "$1,000.42" and "£10,99" into a
//! usable `Currency` instance.
//!
//! ## Example
//!
//! ```
//! extern crate currency;
//!
//! fn main() {
//!     use currency::Currency;
//!
//!     let sock_price = Currency::from_str("$11.99").unwrap();
//!     let toothbrush_price = Currency::from_str("$1.99").unwrap();
//!     let subtotal = sock_price + toothbrush_price;
//!     let tax_rate = 0.07;
//!     let total = &subtotal + (&subtotal * tax_rate);
////!     assert_eq!(total.to_str(), "$14.95") TODO
//! }
//! ```
//!
//! ## Limitations
//!
//! This crate cannot lookup conversion data dynamically. It does supply a `convert` function, but
//! the conversion rates will need to be input by the user.

extern crate num;

use std::{ops, fmt, str};

use num::bigint::{BigInt, BigUint, ParseBigIntError, Sign};
use num::Zero;
use num::traits::FromPrimitive;

/// Represents currency through an optional symbol and amount of coin.
///
/// Every 100 coins represents a banknote. (coin: 100 => 1.00)
/// A currency is formatted by default as such:
/// `Currency { symbol: Some('$'), coin: 432 }` => "$4.32"
#[derive(Debug, Clone, Hash, Default, PartialEq, Eq, PartialOrd)]
pub struct Currency {
    symbol: Option<char>,
    coin: BigInt
}

impl Currency {
    /// Creates a blank Currency with no symbol and 0 coin.
    pub fn new() -> Self {
        Currency {
            symbol: None,
            coin: BigInt::zero()
        }
    }

    /// Parses a string literal (&str) and attempts to convert it into a currency. Returns
    /// `Ok(Currency)` on a successful conversion, otherwise `Err(ParseCurrencyError)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use currency::Currency;
    ///
    /// let c1 = Currency::from_str("$42.32").unwrap();
    /// let c2 = Currency::from_str("$0.10").unwrap();
    /// assert_eq!(c1 + c2, Currency::from_str("$42.42").unwrap());
    /// ```
    pub fn from_str(s: &str) -> Result<Currency, ParseBigIntError> {
        use std::str::FromStr;
        use num::bigint::{BigUint, Sign};

        fn is_symbol(c: char) -> bool {
            !c.is_digit(10) && c != '-' && c != '.' && c != ','
        }

        fn is_delimiter(c: char) -> bool {
            c == '.' || c == ','
        }

        let mut digits = String::new();
        let mut symbol = None;
        let mut sign = Sign::Plus;

        let mut last_delimiter = None;
        let mut last_streak_len = 0;
        for c in s.chars() {
            if c == '-' && digits.len() == 0 {
                sign = Sign::Minus;
            } else if is_delimiter(c) {
                last_streak_len = 0;
                last_delimiter = Some(c);
            } else if is_symbol(c) {
                if symbol.is_none() {
                    symbol = Some(c);
                }
            } else {
                last_streak_len += 1;
                digits.push(c);
            }
        }

        let unsigned_bigint = if digits.len() > 0 {
            let parse_result = BigUint::from_str(&digits);
            match parse_result {
                Ok(int) => int,
                Err(err) => {
                    println!("{:?}", digits);
                    return Err(err)
                }
            }
        } else {
            BigUint::zero()
        };
        let mut coin = BigInt::from_biguint(sign, unsigned_bigint);

        // decimal adjustment
        if last_delimiter.is_none() || last_streak_len == 3 { // no decimal at all
            let big_int_factor = BigInt::from(100);
            coin = coin * big_int_factor;
        } else if last_streak_len < 2 { // specifying less cents than needed
            let factor = 10u32.pow(2 - last_streak_len);
            let big_int_factor = BigInt::from(factor);
            coin = coin * big_int_factor;
        } else if last_streak_len > 2 { // specifying more cents than we can hold
            let divisor = 10u32.pow(last_streak_len - 2);
            let big_int = BigInt::from(divisor);
            coin = coin / big_int;
        } // else the user has valid cents, no adjustment needed

        let currency = Currency {
            symbol: symbol,
            coin: coin
        };

        Ok(currency)
    }

    /// Returns the `Sign` of the `BigInt` holding the coins.
    pub fn sign(&self) -> Sign {
        self.coin.sign()
    }

    /// Returns the number of coins held in the `Currency` as `&BigInt`.
    ///
    /// Should you need ownership of the returned `BigInt`, call `clone()` on it.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate num;
    /// extern crate currency;
    ///
    /// fn main() {
    ///     use num::traits::ToPrimitive;
    ///     use currency::Currency;
    ///
    ///     let c1 = Currency::new();
    ///     assert_eq!(c1.value().to_u32().unwrap(), 0);
    ///
    ///     let c2 = Currency::from_str("$1.42").unwrap();
    ///     assert_eq!(c2.value().to_u32().unwrap(), 142);
    /// }
    /// ```
    pub fn value(&self) -> &BigInt {
        &self.coin
    }

    /// Returns a new `Currency` by multiplying the coin by the conversion rate and changing the
    /// symbol.
    ///
    /// # Examples
    ///
    /// ```
    /// use currency::Currency;
    ///
    /// let dollars = Currency::from_str("$10.00").unwrap();
    /// let conv_rate = 0.89;
    /// let euros = dollars.convert(0.89, '€');
    /// assert_eq!(euros, Currency::from_str("€8.90").unwrap());
    /// ```
    pub fn convert(&self, conversion_rate: f64, currency_symbol: char) -> Currency {
        let mut result = self * conversion_rate;
        result.symbol = Some(currency_symbol);
        result
    }

    // TODO
    // - to_str with comma delimiting
    // - to_str with euro delimiting
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// fmt trait implementations
///////////////////////////////////////////////////////////////////////////////////////////////////

// /// Allows any Currency to be displayed as a String. The format includes no comma delimiting with a
// /// two digit precision decimal.
// ///
// /// # Formats
// ///
// /// ## Arguments
// ///
// /// `#` display commas
// ///
// /// ## Examples
// ///
// /// {} => No commas, rounded to nearest dollar.
// /// {:#} => Commas, rounded to nearest dollar.
// /// {:#.2} => Commas, with decimal point. (values greater than two will route to this fmt as well)
// /// {:.1} => No commas, rounded to nearest ten cents.
// ///
// /// # Examples
// /// ```
// /// use currency::Currency;
// ///
// /// assert!(Currency(Some('$'), 1210).to_string() == "$12.10");
// /// assert!(Currency(None, 1210).to_string() == "12.10");
// ///
// /// println!("{:#}", Currency(Some('$'), 100099)); // $1,000
// /// println!("{:.2}", Currency(Some('$'), 100099)); //
// /// println!("{:.1}", Currency(Some('$'), 100099));
// /// println!("{:.0}", Currency(Some('$'), 100099)); //
// /// ```
// /// The last line prints:
// /// ```text
// /// "$1000.99"
// /// ```
// impl fmt::Display for Currency { // TODO TODO TODO TODO
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let one_hundred = BigInt::from(100);
//         // TODO cases
//         let cents = &self.coin % one_hundred;
//         let dollars = &self.coin - &cents;
//         match self.symbol {
//             Some(c) => write!(f, "{}{}.{}", c, dollars, cents),
//             None    => write!(f, "{}.{}", dollars, cents),
//         }
//     }
// }

impl str::FromStr for Currency {
    type Err = ParseBigIntError;

    fn from_str(s: &str) -> Result<Currency, ParseBigIntError> {
        Currency::from_str(s)
    }
}

// #[derive(Debug, Clone, PartialEq)]
// pub struct ParseCurrencyError {
//     source: String
// }
//
// impl ParseCurrencyError {
//     fn new(s: &str) -> Self {
//         ParseCurrencyError {
//             source: s.to_string()
//         }
//     }
// }
//
// impl fmt::Display for ParseCurrencyError {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "Could not parse {} into a currency.", self.source)
//     }
// }
//
// impl error::Error for ParseCurrencyError {
//     fn description(&self) -> &str {
//         "Failed to parse currency"
//     }
// }

// TODO
// /// Identical to the implementation of Display, but replaces the "." with a ",". Access this
// /// formating by using "{:e}".
// ///
// /// # Examples
// /// ```
// /// use currency::Currency;
// ///
// /// println!("{:e}", Currency(Some('£'), 100099));
// /// ```
// /// The last line prints the following:
// /// ```text
// /// "£1000,99"
// /// ```
// impl fmt::LowerExp for Currency {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "{}", format!("{}", self).replace(".", ","))
//     }
// }

///////////////////////////////////////////////////////////////////////////////////////////////////
// ops trait implementations
// macros based on bigint: http://rust-num.github.io/num/src/num_bigint/bigint/src/lib.rs.html
///////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! impl_all_trait_combinations_for_currency {
    ($module:ident::$imp:ident, $method:ident) => {
        impl<'a, 'b> $module::$imp<&'b Currency> for &'a Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'b Currency) -> Currency {
                if self.symbol == other.symbol {
                    Currency {
                        symbol: self.symbol.clone(),
                        coin: self.coin.clone().$method(other.coin.clone())
                    }
                } else {
                    panic!("Cannot do arithmetic on two different types of currency.");
                }
            }
        }

        impl<'a> $module::$imp<Currency> for &'a Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: Currency) -> Currency {
                if self.symbol == other.symbol {
                    Currency {
                        symbol: self.symbol.clone(),
                        coin: self.coin.clone().$method(other.coin)
                    }
                } else {
                    panic!("Cannot do arithmetic on two different types of currency.");
                }
            }
        }

        impl<'a> $module::$imp<&'a Currency> for Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'a Currency) -> Currency {
                if self.symbol == other.symbol {
                    Currency {
                        symbol: self.symbol,
                        coin: self.coin.$method(other.coin.clone())
                    }
                } else {
                    panic!("Cannot do arithmetic on two different types of currency.");
                }
            }
        }

        impl $module::$imp<Currency> for Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: Currency) -> Currency {
                if self.symbol == other.symbol {
                    Currency {
                        symbol: self.symbol,
                        coin: self.coin.$method(other.coin)
                    }
                } else {
                    panic!("Cannot do arithmetic on two different types of currency.");
                }
            }
        }
    }
}

impl_all_trait_combinations_for_currency!(ops::Add, add);
impl_all_trait_combinations_for_currency!(ops::Sub, sub);
// impl_all_trait_combinations_for_currency!(ops::Mul, mul); TODO decide whether this should exist

// other type must implement Into<BigInt>
macro_rules! impl_all_trait_combinations_for_currency_into_bigint {
    ($module:ident::$imp:ident, $method:ident, $other:ty) => {
        impl<'a, 'b> $module::$imp<&'b $other> for &'a Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'b $other) -> Currency {
                let big_int: BigInt = other.clone().into();
                Currency {
                    symbol: self.symbol.clone(),
                    coin: self.coin.clone().$method(big_int)
                }
            }
        }

        impl<'a> $module::$imp<$other> for &'a Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: $other) -> Currency {
                let big_int: BigInt = other.into();
                Currency {
                    symbol: self.symbol.clone(),
                    coin: self.coin.clone().$method(big_int)
                }
            }
        }

        impl<'a> $module::$imp<&'a $other> for Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'a $other) -> Currency {
                let big_int: BigInt = other.clone().into();
                Currency {
                    symbol: self.symbol,
                    coin: self.coin.$method(big_int)
                }
            }
        }

        impl $module::$imp<$other> for Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: $other) -> Currency {
                let big_int: BigInt = other.into();
                Currency {
                    symbol: self.symbol,
                    coin: self.coin.$method(big_int)
                }
            }
        }

        impl<'a, 'b> $module::$imp<&'b Currency> for &'a $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'b Currency) -> Currency {
                let big_int: BigInt = self.clone().into();
                Currency {
                    symbol: other.symbol.clone(),
                    coin: other.coin.clone().$method(big_int)
                }
            }
        }

        impl<'a> $module::$imp<Currency> for &'a $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: Currency) -> Currency {
                let big_int: BigInt = self.clone().into();
                Currency {
                    symbol: other.symbol,
                    coin: other.coin.$method(big_int)
                }
            }
        }

        impl<'a> $module::$imp<&'a Currency> for $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'a Currency) -> Currency {
                let big_int: BigInt = self.into();
                Currency {
                    symbol: other.symbol.clone(),
                    coin: other.coin.clone().$method(big_int)
                }
            }
        }

        impl $module::$imp<Currency> for $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: Currency) -> Currency {
                let big_int: BigInt = self.into();
                Currency {
                    symbol: other.symbol,
                    coin: other.coin.$method(big_int)
                }
            }
        }
    }
}

impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, BigUint);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, u8);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, u16);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, u32);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, u64);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, usize);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, i8);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, i16);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, i32);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, i64);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Mul, mul, isize);

impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, BigUint);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, u8);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, u16);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, u32);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, u64);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, usize);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, i8);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, i16);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, i32);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, i64);
impl_all_trait_combinations_for_currency_into_bigint!(ops::Div, div, isize);

macro_rules! impl_all_trait_combinations_for_currency_conv_bigint {
    ($module:ident::$imp:ident, $method:ident, $other:ty, $conv_method:ident) => {
        impl<'a, 'b> $module::$imp<&'b $other> for &'a Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'b $other) -> Currency {
                let big_int = BigInt::$conv_method(other.clone() * 100.0).unwrap();
                Currency {
                    symbol: self.symbol.clone(),
                    coin: self.coin.clone().$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl<'a> $module::$imp<$other> for &'a Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: $other) -> Currency {
                let big_int = BigInt::$conv_method(other * 100.0).unwrap();
                Currency {
                    symbol: self.symbol.clone(),
                    coin: self.coin.clone().$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl<'a> $module::$imp<&'a $other> for Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'a $other) -> Currency {
                let big_int = BigInt::$conv_method(other.clone() * 100.0).unwrap();
                Currency {
                    symbol: self.symbol,
                    coin: self.coin.$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl $module::$imp<$other> for Currency {
            type Output = Currency;

            #[inline]
            fn $method(self, other: $other) -> Currency {
                let big_int = BigInt::$conv_method(other * 100.0).unwrap();
                Currency {
                    symbol: self.symbol,
                    coin: self.coin.$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl<'a, 'b> $module::$imp<&'b Currency> for &'a $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'b Currency) -> Currency {
                let big_int = BigInt::$conv_method(self.clone() * 100.0).unwrap();
                Currency {
                    symbol: other.symbol.clone(),
                    coin: other.coin.clone().$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl<'a> $module::$imp<Currency> for &'a $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: Currency) -> Currency {
                let big_int = BigInt::$conv_method(self.clone() * 100.0).unwrap();
                Currency {
                    symbol: other.symbol,
                    coin: other.coin.$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl<'a> $module::$imp<&'a Currency> for $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: &'a Currency) -> Currency {
                let big_int = BigInt::$conv_method(self * 100.0).unwrap();
                Currency {
                    symbol: other.symbol.clone(),
                    coin: other.coin.clone().$method(big_int) / BigInt::from(100)
                }
            }
        }

        impl $module::$imp<Currency> for $other {
            type Output = Currency;

            #[inline]
            fn $method(self, other: Currency) -> Currency {
                let big_int = BigInt::$conv_method(self * 100.0).unwrap();
                Currency {
                    symbol: other.symbol,
                    coin: other.coin.$method(big_int) / BigInt::from(100)
                }
            }
        }
    }
}

impl_all_trait_combinations_for_currency_conv_bigint!(ops::Mul, mul, f32, from_f32);
impl_all_trait_combinations_for_currency_conv_bigint!(ops::Mul, mul, f64, from_f64);

impl_all_trait_combinations_for_currency_conv_bigint!(ops::Div, div, f32, from_f32);
impl_all_trait_combinations_for_currency_conv_bigint!(ops::Div, div, f64, from_f64);

/// Overloads the '/' operator between two borrowed Currency objects.
///
/// # Panics
/// Panics if they aren't the same type of currency, as denoted by the currency's symbol.
impl<'a, 'b> ops::Div<&'b Currency> for &'a Currency {
    type Output = BigInt;

    fn div(self, other: &'b Currency) -> BigInt {
        if self.symbol == other.symbol {
            self.coin.clone() / other.coin.clone()
        } else {
            panic!("Cannot divide two different types of currency.");
        }
    }
}

/// Overloads the '/' operator between a borrowed Currency object and an owned one.
///
/// # Panics
/// Panics if they aren't the same type of currency, as denoted by the currency's symbol.
impl<'a> ops::Div<Currency> for &'a Currency {
    type Output = BigInt;

    fn div(self, other: Currency) -> BigInt {
        if self.symbol == other.symbol {
            self.coin.clone() / other.coin
        } else {
            panic!("Cannot divide two different types of currency.");
        }
    }
}

/// Overloads the '/' operator between an owned Currency object and a borrowed one.
///
/// # Panics
/// Panics if they aren't the same type of currency, as denoted by the currency's symbol.
impl<'a> ops::Div<&'a Currency> for Currency {
    type Output = BigInt;

    fn div(self, other: &'a Currency) -> BigInt {
        if self.symbol == other.symbol {
            self.coin / other.coin.clone()
        } else {
            panic!("Cannot divide two different types of currency.");
        }
    }
}

/// Overloads the '/' operator between two owned Currency objects.
///
/// # Panics
/// Panics if they aren't the same type of currency, as denoted by the currency's symbol.
impl ops::Div<Currency> for Currency {
    type Output = BigInt;

    fn div(self, other: Currency) -> BigInt {
        if self.symbol == other.symbol {
            self.coin / other.coin
        } else {
            panic!("Cannot divide two different types of currency.");
        }
    }
}

impl ops::Neg for Currency {
    type Output = Currency;

    fn neg(self) -> Currency {
        Currency {
            symbol: self.symbol,
            coin: -self.coin
        }
    }
}

impl<'a> ops::Neg for &'a Currency {
    type Output = Currency;

    fn neg(self) -> Currency {
        Currency {
            symbol: self.symbol.clone(),
            coin: -self.coin.clone()
        }
    }
}

// TODO
// - rem
// - signed

#[cfg(test)]
mod tests {
    use super::Currency;
    use num::bigint::BigInt;

    #[test]
    fn test_from_str() {
        use std::str::FromStr;

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(1210) };
        let actual = Currency::from_str("$12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$12.100000").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$12.1").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: None, coin: BigInt::from(1210) };
        let actual = Currency::from_str("12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("12.100000").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("12.1").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(121000) };
        let actual = Currency::from_str("$1210").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$1,210").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$1,210.00").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$1210.").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$1,210.0").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$1.210,0").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(1200099) };
        let actual = Currency::from_str("$12,000.99").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('£'), coin: BigInt::from(1200099) };
        let actual = Currency::from_str("£12,000.99").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(-1210) };
        let actual = Currency::from_str("-$12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$-12.10").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('€'), coin: BigInt::from(-12000) };
        let actual = Currency::from_str("-€120.00").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("-€120").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("-€-120.0").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("-€120").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('€'), coin: BigInt::from(0) };
        let actual = Currency::from_str("€0").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("€00.00").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("€.00000000").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("€0.0").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("€000,000.00").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("€000,000").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("€").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(1000) };
        let actual = Currency::from_str("$10.0001").unwrap();
        assert_eq!(expected, actual);

        // TODO rounding
        // let expected = Currency { symbol: Some('$'), coin: BigInt::from(1001) };
        // let actual = Currency::from_str("$10.0099").unwrap();
        // assert_eq!(expected, actual);
    }

    #[test]
    fn test_eq() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(1210) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(1210) };
        let c = Currency { symbol: Some('$'), coin: BigInt::from(1251) };

        assert!(a == b);
        assert!(b == b);
        assert!(b == a);
        assert!(a != c);
    }

    #[test]
    fn test_ord() {
        use std::cmp::Ordering;

        let a = Currency { symbol: Some('$'), coin: BigInt::from(1210) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(1211) };
        let c = Currency { symbol: Some('$'), coin: BigInt::from(1311) };
        let d = Currency { symbol: Some('$'), coin: BigInt::from(1210) };

        assert_eq!(a.partial_cmp(&b), Some(Ordering::Less));
        assert_eq!(a.partial_cmp(&c), Some(Ordering::Less));
        assert_eq!(a.partial_cmp(&d), Some(Ordering::Equal));
        assert_eq!(c.partial_cmp(&a), Some(Ordering::Greater));

        assert!(a < b);
        assert!(a < c);
        assert!(a <= a);
        assert!(a <= c);
        assert!(b > a);
        assert!(c > a);
        assert!(a >= a);
        assert!(c >= a);
    }

    #[test]
    fn test_add() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(1211) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(1311) };
        let expected_sum = Currency { symbol: Some('$'), coin: BigInt::from(2522) };
        let actual_sum = a + b;
        assert_eq!(expected_sum, actual_sum);
    }

    #[test]
    fn test_add_commutative() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(1211) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(1311) };
        assert!(&a + &b == &b + &a);
    }

    #[test]
    fn test_sub() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(1211) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(1311) };

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(-100) };
        let actual = &a - &b;
        assert_eq!(expected, actual);

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(100) };
        let actual = b - a;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_mul() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(1211) };
        let f = 0.97;
        let expected = Currency { symbol: Some('$'), coin: BigInt::from(1174) };
        let actual = a * f;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_mul_commutative() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(1211) };
        let f = 0.97;
        assert_eq!(&a * &f, &f * &a);
    }

    #[test]
    fn test_div() {
        let a = Currency { symbol: Some('$'), coin: BigInt::from(2500) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(500) };
        let expected = BigInt::from(5);
        let actual = a / b;
        assert_eq!(expected, actual);

        let a = Currency { symbol: Some('$'), coin: BigInt::from(3248) };
        let b = Currency { symbol: Some('$'), coin: BigInt::from(888) };
        let expected = BigInt::from(3);
        let actual = a / b;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_neg() {
        let c = Currency { symbol: Some('$'), coin: BigInt::from(3248) };
        let expected = Currency { symbol: Some('$'), coin: BigInt::from(-3248) };
        let actual = -c;
        assert_eq!(expected, actual);

        let c = Currency { symbol: Some('$'), coin: BigInt::from(-3248) };
        let expected = Currency { symbol: Some('$'), coin: BigInt::from(3248) };
        let actual = -c;
        assert_eq!(expected, actual);

        let c = Currency { symbol: Some('$'), coin: BigInt::from(0) };
        let expected = Currency { symbol: Some('$'), coin: BigInt::from(0) };
        let actual = -c;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_convert() {
        let dollars = Currency::from_str("$12.50").unwrap();
        let euro_conversion_rate = 0.89;
        let euros = dollars.convert(euro_conversion_rate, '€');
        let expected = Currency { symbol: Some('€'), coin: BigInt::from(1112) };
        assert_eq!(expected, euros);
    }

    // #[test]
    // fn display_works() {
    // 	assert!(format!("{:?}", Currency { symbol: None, coin: 10 }) == "Currency(None, 10)");
    //
    // 	assert!(Currency { symbol: None, coin: 1210 }.to_string() == "12.10");
    //     assert!(Currency { symbol: Some('$'), coin: 1210 }.to_string() == "$12.10");
    //     assert!(Currency { symbol: Some('$'), coin: 100010 }.to_string() == "$1000.10");
    //
    // 	assert!(format!("{:e}", Currency { symbol: Some('£'), coin: 100000 }) == "£1000,00");
    // }
}
