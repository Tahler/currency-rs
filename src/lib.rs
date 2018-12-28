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
//!     assert_eq!(format!("{}", total), "$14.95");
//! }
//! ```
//!
//! ## Limitations
//!
//! This crate cannot lookup conversion data dynamically. It does supply a `convert` function, but
//! the conversion rates will need to be input by the user.
//!
//! This crate also does not handle rounding or precision. Values are truncated during
//! multiplication, division, and extra precision in a parse (such as gas prices).

extern crate num;

use std::{ops, fmt, str, error};

use num::bigint::{BigInt, BigUint, Sign};
use num::Zero;
use num::traits::FromPrimitive;

const DECIMAL_PLACES: usize = 2;
const SECTION_LEN: usize = 3; // 1,323.00 <- "323" is a section

/// Represents currency through an optional symbol and amount of coin.
///
/// Every 100 coins represents a banknote. (coin: 100 => 1.00)
#[derive(Debug, Clone, Hash, Default, PartialEq, Eq, PartialOrd)]
pub struct Currency {
    symbol: String,
    coin: BigInt
}

impl Currency {
    /// Creates a blank Currency with no symbol and 0 coin.
    pub fn new() -> Self {
        Currency {
            symbol: "".into(),
            coin: BigInt::zero()
        }
    }

    /// Creates a `Currency` from the specified values.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use currency::Currency;
    /// 
    /// let c = Currency::from(1000, '$');
    /// assert_eq!(c, Currency::from_str("$10.00").unwrap());
    /// ```
    pub fn from(coin: impl Into<BigInt>, symbol: impl ToString) -> Currency {
        Currency {
            symbol: symbol.to_string(),
            coin: coin.into(),
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
    pub fn from_str(s: &str) -> Result<Currency, ParseCurrencyError> {
        use std::str::FromStr;
        use num::bigint::{BigUint, Sign};

        let err = ParseCurrencyError::new(s);

        fn is_symbol(c: char) -> bool {
            !c.is_digit(10) && c != '-' && c != '.' && c != ',' && c != ')'
        }

        fn is_delimiter(c: char) -> bool {
            c == '.' || c == ','
        }

        let mut digits = String::new();
        let mut symbol = String::new();
        let mut sign = Sign::Plus;

        let mut symbol_ended = false;

        let mut last_delimiter = None;
        let mut last_streak_len = 0;
        for c in s.chars() {
            if (c  == '(' || c == '-') && digits.len() == 0 {
                if !symbol.is_empty() {
                    symbol_ended = true;
                }
                sign = Sign::Minus;
            } else if is_delimiter(c) {
                if !symbol.is_empty() {
                    symbol_ended = true;
                }
                last_streak_len = 0;
                last_delimiter = Some(c);
            } else if is_symbol(c) {
                if !symbol_ended {
                    symbol.push(c);
                }
            } else if c == ')' {
                break;
            } else {
                symbol_ended = true;
                last_streak_len += 1;
                digits.push(c);
            }
        }

        let unsigned_bigint = if digits.len() > 0 {
            let parse_result = BigUint::from_str(&digits);
            match parse_result {
                Ok(int) => int,
                Err(_) => {
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

    /// Returns the symbol of the `Currency` as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate currency;
    ///
    /// fn main() {
    ///     use currency::Currency;
    ///
    ///     let c1 = Currency::from_str("USD1.00").unwrap();
    ///     assert_eq!(c1.symbol(), "USD");
    ///     
    ///     let c2 = Currency::from_str("€1.00").unwrap();
    ///     assert_eq!(c2.symbol(), "€");
    /// 
    ///     let c3 = Currency::from_str("1.00").unwrap();
    ///     assert_eq!(c3.symbol(), "");
    /// }
    /// ```
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    /// Sets the symbol of the `Currency`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate currency;
    ///
    /// fn main() {
    ///     use currency::Currency;
    ///
    ///     let mut c = Currency::from_str("USD1.00").unwrap();
    ///     c.set_symbol('$');
    ///     assert_eq!(c.symbol(), "$");
    ///     assert_eq!(c, Currency::from_str("$1.00").unwrap());
    /// }
    /// ```
    pub fn set_symbol(&mut self, symbol: impl ToString) {
        self.symbol = symbol.to_string();
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
    pub fn convert(&self, conversion_rate: f64, currency_symbol: impl ToString) -> Currency {
        let mut result = self * conversion_rate;
        result.symbol = currency_symbol.to_string();
        result
    }

    // TODO
    // - to_str with comma delimiting
    // - to_str with euro delimiting
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// fmt trait implementations
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Allows any Currency to be displayed as a String. The format includes comma delimiting with a
/// two digit precision decimal.
///
/// # Example
///
/// ```
/// use currency::Currency;
///
/// let dollars = Currency::from_str("$12.10").unwrap();
/// assert_eq!(dollars.to_string(), "$12.10");
///
/// let euros = Currency::from_str("£1.000").unwrap();
/// assert_eq!(format!("{:e}", euros), "£1.000,00");
/// ```
impl fmt::Display for Currency {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use num::traits::Signed;

        let mut result = String::new();

        if self.coin.sign() == Sign::Minus {
            result.push('-');
        }

        result.push_str(&self.symbol);

        let digit_str = self.coin.abs().to_str_radix(10);

        // put symbol before first digit
        let n_digits = digit_str.len();
        if n_digits <= DECIMAL_PLACES { // gotta put 0.xx or 0.0x
            result.push_str("0.");
            if n_digits == 1 {
                result.push('0');
            }
            result.push_str(&digit_str);
        } else {
            let n_before_dec = n_digits - DECIMAL_PLACES;
            let int_digit_str = &digit_str[0..n_before_dec];
            let dec_digit_str = &digit_str[n_before_dec..n_digits];

            let first_section_len = n_before_dec % SECTION_LEN;
            let mut counter = if first_section_len != 0 {
                SECTION_LEN - first_section_len
            } else {
                0
            };
            for digit in int_digit_str.chars() {
                if counter == SECTION_LEN {
                    counter = 0;
                    result.push(',');
                }
                result.push(digit);
                counter += 1;
            }
            result.push('.');
            result.push_str(dec_digit_str);
        }

        write!(f, "{}", result)
    }
}

impl str::FromStr for Currency {
    type Err = ParseCurrencyError;

    fn from_str(s: &str) -> Result<Currency, ParseCurrencyError> {
        Currency::from_str(s)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseCurrencyError {
    source: String
}

impl ParseCurrencyError {
    fn new(s: &str) -> Self {
        ParseCurrencyError {
            source: s.to_string()
        }
    }
}

impl fmt::Display for ParseCurrencyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Could not parse {} into a currency.", self.source)
    }
}

impl error::Error for ParseCurrencyError {
    fn description(&self) -> &str {
        "Failed to parse currency"
    }
}

/// Identical to the implementation of Display, but replaces the "." with a ",". Access this
/// formatting by using "{:e}".
///
/// # Example
///
/// ```
/// use currency::Currency;
///
/// let euros = Currency::from_str("£1000,99").unwrap();
/// println!("{:e}", euros);
/// ```
/// Which prints:
/// ```text
/// "£1.000,99"
/// ```
impl fmt::LowerExp for Currency {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let temp = format!("{}", self).replace(".", "x");
        let almost = temp.replace(",", ".");
        let there_we_go = almost.replace("x", ",");
        write!(f, "{}", there_we_go)
    }
}

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
        let expected = Currency { symbol: "$".into(), coin: BigInt::from(1210) };
        let actual = Currency::from_str("$12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$12.100000").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$12.1").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "".into(), coin: BigInt::from(1210) };
        let actual = Currency::from_str("12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("12.100000").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("12.1").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "".into(), coin: BigInt::from(-1210) };
        let actual = Currency::from_str("(12.10)").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(121000) };
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

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(1200099) };
        let actual = Currency::from_str("$12,000.99").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "£".into(), coin: BigInt::from(1200099) };
        let actual = Currency::from_str("£12,000.99").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(-1200099) };
        let actual = Currency::from_str("-(-$-12,000.99").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("($12,000.99)").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$(12,000.99)").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(-1210) };
        let actual = Currency::from_str("-$12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("$-12.10").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("($12.10)").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("($12.1)").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "€".into(), coin: BigInt::from(-12000) };
        let actual = Currency::from_str("-€120.00").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("-€120").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("-€-120.0").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("-€120").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("(€120)").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "USD".into(), coin: BigInt::from(-12000) };
        let actual = Currency::from_str("-USD120").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("USD-120").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("(USD1€20EUR)JPY").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("USD(D120)").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "".into(), coin: BigInt::from(12000) };
        let actual = Currency::from_str("120USD").unwrap();
        assert_eq!(expected, actual);
        let actual = Currency::from_str("1U2S0D").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "€".into(), coin: BigInt::from(0) };
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
        let actual = Currency::from_str("€)10.99asdf").unwrap();
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(1000) };
        let actual = Currency::from_str("$10.0001").unwrap();
        assert_eq!(expected, actual);

        // TODO rounding
        // let expected = Currency { symbol: "$".into(), coin: BigInt::from(1001) };
        // let actual = Currency::from_str("$10.0099").unwrap();
        // assert_eq!(expected, actual);
    }

    #[test]
    fn test_eq() {
        let a = Currency { symbol: "$".into(), coin: BigInt::from(1210) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(1210) };
        let c = Currency { symbol: "$".into(), coin: BigInt::from(1251) };

        assert!(a == b);
        assert!(b == b);
        assert!(b == a);
        assert!(a != c);
    }

    #[test]
    fn test_ord() {
        use std::cmp::Ordering;

        let a = Currency { symbol: "$".into(), coin: BigInt::from(1210) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(1211) };
        let c = Currency { symbol: "$".into(), coin: BigInt::from(1311) };
        let d = Currency { symbol: "$".into(), coin: BigInt::from(1210) };

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
        let a = Currency { symbol: "$".into(), coin: BigInt::from(1211) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(1311) };
        let expected_sum = Currency { symbol: "$".into(), coin: BigInt::from(2522) };
        let actual_sum = a + b;
        assert_eq!(expected_sum, actual_sum);
    }

    #[test]
    fn test_add_commutative() {
        let a = Currency { symbol: "$".into(), coin: BigInt::from(1211) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(1311) };
        assert!(&a + &b == &b + &a);
    }

    #[test]
    fn test_sub() {
        let a = Currency { symbol: "$".into(), coin: BigInt::from(1211) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(1311) };

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(-100) };
        let actual = &a - &b;
        assert_eq!(expected, actual);

        let expected = Currency { symbol: "$".into(), coin: BigInt::from(100) };
        let actual = b - a;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_mul() {
        let a = Currency { symbol: "$".into(), coin: BigInt::from(1211) };
        let f = 0.97;
        let expected = Currency { symbol: "$".into(), coin: BigInt::from(1174) };
        let actual = a * f;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_mul_commutative() {
        let a = Currency { symbol: "$".into(), coin: BigInt::from(1211) };
        let f = 0.97;
        assert_eq!(&a * &f, &f * &a);
    }

    #[test]
    fn test_div() {
        let a = Currency { symbol: "$".into(), coin: BigInt::from(2500) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(500) };
        let expected = BigInt::from(5);
        let actual = a / b;
        assert_eq!(expected, actual);

        let a = Currency { symbol: "$".into(), coin: BigInt::from(3248) };
        let b = Currency { symbol: "$".into(), coin: BigInt::from(888) };
        let expected = BigInt::from(3);
        let actual = a / b;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_neg() {
        let c = Currency { symbol: "$".into(), coin: BigInt::from(3248) };
        let expected = Currency { symbol: "$".into(), coin: BigInt::from(-3248) };
        let actual = -c;
        assert_eq!(expected, actual);

        let c = Currency { symbol: "$".into(), coin: BigInt::from(-3248) };
        let expected = Currency { symbol: "$".into(), coin: BigInt::from(3248) };
        let actual = -c;
        assert_eq!(expected, actual);

        let c = Currency { symbol: "$".into(), coin: BigInt::from(0) };
        let expected = Currency { symbol: "$".into(), coin: BigInt::from(0) };
        let actual = -c;
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_convert() {
        let dollars = Currency::from_str("$12.50").unwrap();
        let euro_conversion_rate = 0.89;
        let euros = dollars.convert(euro_conversion_rate, '€');
        let expected = Currency { symbol: '€'.to_string(), coin: BigInt::from(1112) };
        assert_eq!(expected, euros);
    }

    #[test]
    fn test_display() {
        use num::traits::Num;

        assert_eq!(
            Currency { symbol: "$".into(), coin: BigInt::from(0) }.to_string(),
            "$0.00"
        );

        assert_eq!(
            Currency { symbol: "$".into(), coin: BigInt::from(-1) }.to_string(),
            "-$0.01"
        );

        assert_eq!(
            Currency { symbol: "".into(), coin: BigInt::from(11) }.to_string(),
            "0.11"
        );

        assert_eq!(
            Currency { symbol: "".into(), coin: BigInt::from(1210) }.to_string(),
            "12.10"
        );

        assert_eq!(
            Currency { symbol: "$".into(), coin: BigInt::from(1210) }.to_string(),
            "$12.10"
        );

        assert_eq!(
            Currency { symbol: "".into(), coin: BigInt::from(10000) }.to_string(),
            "100.00"
        );

        assert_eq!(
            Currency { symbol: "£".into(), coin: BigInt::from(100010) }.to_string(),
            "£1,000.10"
        );

        assert_eq!(
            Currency { symbol: "USD".into(), coin: BigInt::from(100010) }.to_string(),
            "USD1,000.10"
        );

        assert_eq!(
            Currency { symbol: "USD ".into(), coin: BigInt::from(100010) }.to_string(),
            "USD 1,000.10"
        );

        assert_eq!(
            Currency {
                symbol: "$".into(),
                coin: BigInt::from_str_radix("123456789001", 10).unwrap()
            }.to_string(),
            "$1,234,567,890.01"
        );

        assert_eq!(
            Currency {
                symbol: "$".into(),
                coin: BigInt::from_str_radix("-123456789001", 10).unwrap()
            }.to_string(),
            "-$1,234,567,890.01"
        );
    }

    #[test]
    fn test_foreign_display() {
        assert_eq!(
            format!("{:e}", Currency { symbol: "£".into(), coin: BigInt::from(100000) }),
            "£1.000,00"
        );

        assert_eq!(
            format!("{:e}", Currency { symbol: "£".into(), coin: BigInt::from(123400101) }),
            "£1.234.001,01"
        );
    }
}
