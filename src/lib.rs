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
// //! //TODO
// //! ## Example
// //! ```
// //! extern crate currency;
// //!
// //! fn main() {
// //!     use currency::Currency;
// //!
// //!     let sock_price = Currency::from_str("$11.99");
// //!     let toothbrush_price = Currency::from_str("$1.99");
// //!     let subtotal = sock_price + toothbrush_price;
// //!     let tax_rate = 0.07;
// //!     let total = subtotal + (subtotal * tax_rate);
// //!     assert_eq!(total.to_str(), "$14.96")
// //! }
// //! ```
//!
//! ## Limitations
//!
//! This crate cannot lookup conversion data dynamically. It does supply a `convert` function, but
//! the conversion rates will need to be input by the user.

extern crate num;

use std::{ops, cmp, fmt, str};

use num::bigint::{BigInt, ParseBigIntError, Sign};
use num::Zero;

/// Represents currency through an optional symbol and amount of coin.
///
/// Every 100 coins represents a banknote. (coin: 100 => 1.00)
/// A currency is formatted by default as such:
/// `Currency { symbol: Some('$'), coin: 432 }` => "$4.32"
#[derive(Debug, Clone, Hash, Default)]
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

    /// Parses a string literal (&str) and attempts to convert it into a currency. Returns
    /// `Ok(Currency)` on a successful conversion, otherwise `Err(ParseCurrencyError)`.
    ///
    /// `from_str` can be unexpectedly simple, so be be aware of the following rules:
    ///
    /// 1. If the string contains a '-' before any digits, the Currency will be negative.
    /// 2. The first non-digit character (excluding '-', ',' and '.') will become the Currency's
    /// symbol.
    /// 3. Only the final '.' or ',' is significant. If it is not followed by two digits (the
    /// "cents"), it is treated as if there were a ".00" or ",00" after it. TODO
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

    // TODO
    // - to_str with comma delimiting
    // - to_str with euro delimiting
    // - conversion with supplied conversion rate
    // - tax
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
// cmp trait implementations
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Overloads the '==' operator for Currency objects.
///
/// # Panics
/// Panics if the two comparators are different types of currency, as denoted by the Currency's
/// symbol.
impl PartialEq<Currency> for Currency {
    fn eq(&self, other: &Currency) -> bool {
        self.symbol == other.symbol && self.coin == other.coin
    }

    fn ne(&self, other: &Currency) -> bool {
        self.symbol != other.symbol || self.coin != other.coin
    }
}

/// Overloads the order operators for Currency objects.
///
/// These operators include '<', '<=', '>', and '>='.
///
/// # Panics
/// Panics if the two comparators are different types of currency, as denoted by
/// the Currency's symbol.
impl PartialOrd<Currency> for Currency {
    fn partial_cmp(&self, other: &Currency) -> Option<cmp::Ordering> {
        if self.symbol == other.symbol {
            self.coin.partial_cmp(&other.coin)
        } else {
            None
        }
    }

    fn lt(&self, other: &Currency) -> bool {
        if self.symbol == other.symbol {
            self.coin.lt(&other.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }

    fn le(&self, other: &Currency) -> bool {
        if self.symbol == other.symbol {
            self.coin.le(&other.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }

    fn gt(&self, other: &Currency) -> bool {
        if self.symbol == other.symbol {
            self.coin.gt(&other.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }

    fn ge(&self, other: &Currency) -> bool {
        if self.symbol == other.symbol {
            self.coin.ge(&other.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// ops trait implementations
// macros copied from bigint: http://rust-num.github.io/num/src/num_bigint/bigint/src/lib.rs.html
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

/// Overloads the '*' operator between two borrowed Currency objects.
///
/// # Panics
/// Panics if the factors are two different types of currency, as denoted by the Currency's symbol.
impl<'a, 'b> ops::Mul<&'b Currency> for &'a Currency {
    type Output = Currency;

    fn mul(self, other: &Currency) -> Currency {
        if self.symbol == other.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.clone().mul(other.coin.clone())
            }
        } else {
            panic!("Cannot multiply two different types of currency.");
        }
    }
}

/// Overloads the '*' operator between a borrowed Currency object and an owned one.
///
/// # Panics
/// Panics if the factors are two different types of currency, as denoted by the Currency's symbol.
impl<'a> ops::Mul<Currency> for &'a Currency {
    type Output = Currency;

    fn mul(self, other: Currency) -> Currency {
        if self.symbol == other.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.clone().mul(other.coin)
            }
        } else {
            panic!("Cannot multiply two different types of currency.");
        }
    }
}

/// Overloads the '*' operator between an owned Currency object and a borrowed one.
///
/// # Panics
/// Panics if the factors are two different types of currency, as denoted by the Currency's symbol.
impl<'a> ops::Mul<&'a Currency> for Currency {
    type Output = Currency;

    fn mul(self, other: &Currency) -> Currency {
        if self.symbol == other.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.mul(other.coin.clone())
            }
        } else {
            panic!("Cannot multiply two different types of currency.");
        }
    }
}

/// Overloads the '*' operator between two owned Currency objects.
///
/// # Panics
/// Panics if the factors are two different types of currency, as denoted by the Currency's symbol.
impl ops::Mul<Currency> for Currency {
    type Output = Currency;

    fn mul(self, other: Currency) -> Currency {
        if self.symbol == other.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.mul(other.coin)
            }
        } else {
            panic!("Cannot multiply two different types of currency.");
        }
    }
}

// /// Overloads the '*' operator between a Currency object and an Into<BigInt>.
// ///
// /// Allows a Currency to be multiplied by any type that can be converted to a BigInt.
// impl<N: Into<BigInt>> ops::Mul<N> for Currency {
//     type Output = Currency;
//
//     fn mul(self, other: N) -> Currency {
//         Currency {
//             symbol: self.symbol,
//             coin: self.coin.mul(BigInt::from(other))
//         }
//     }
// }

/// Overloads the '*' operator between a Currency object and an Into<BigInt>.
///
/// Allows a Currency to be multiplied by any type that can be converted to a BigInt.
// impl<N: Into<BigInt>> ops::Mul<Currency> for N {
//     type Output = Currency;
//
//     fn mul(self, other: N) -> Currency {
//         // Currency {
//         //     symbol: self.symbol,
//         //     coin: self.coin.mul(BigInt::from(other))
//         // }
//         Currency::new()
//     }
// }


// TODO mul for each num type, both ways

// /// Overloads the '/ operator between two owned Currency objects.
// ///
// /// # Panics
// /// Panics if the factors are two different types of currency, as denoted by the Currency's symbol.
// impl ops::Div<Currency> for Currency {
//     type Output = BigInt;
//
//     fn mul(self, other: Currency) -> Currency {
//         if self.symbol == other.symbol {
//             Currency {
//                 symbol: self.symbol,
//                 coin: self.coin.mul(other.coin)
//             }
//         } else {
//             panic!("Cannot multiply two different types of currency.");
//         }
//     }
// }


// TODO
// - neg
// - rem

#[cfg(test)]
mod tests {
    use super::Currency;
    use num::bigint::BigInt;

    #[test]
    fn test_from_str() {
        use std::str::FromStr;
// use num::bigint::BigUint;
//         BigUint::from_str("01210").unwrap();

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

        let expected = Currency { symbol: Some('$'), coin: BigInt::from(1001) };
        let actual = Currency::from_str("$10.0099").unwrap();
        assert_eq!(expected, actual);
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

    //
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
