use std::{ops, cmp, fmt, str, error};

use super::num::bigint::BigInt;
use super::num::Zero;

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
    ///
    /// # Examples
    /// ```
    /// extern crate currency;
    /// use currency::Currency;
    ///
    /// let mut c = Currency::new();
    /// println!("{}", c); // "0"
    /// println!("{:.2}", c); // "0.00"
    /// ```
    pub fn new() -> Self {
        Currency {
            symbol: None,
            coin: BigInt::zero()
        }
    }

    // TODO
    // - to_str with comma delimiting
    // - to_str with euro delimiting
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// fmt trait implementations
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Allows any Currency to be displayed as a String. The format includes no comma delimiting with a
/// two digit precision decimal.
///
/// # Formats
///
/// ## Arguments
///
/// `#` display commas
///
/// ## Examples
///
/// {} => No commas, rounded to nearest dollar.
/// {:#} => Commas, rounded to nearest dollar.
/// {:#.2} => Commas, with decimal point. (values greater than two will route to this fmt as well)
/// {:.1} => No commas, rounded to nearest ten cents.
///
/// # Examples
/// ```
/// use currency::Currency;
///
/// assert!(Currency(Some('$'), 1210).to_string() == "$12.10");
/// assert!(Currency(None, 1210).to_string() == "12.10");
///
/// println!("{:#}", Currency(Some('$'), 100099)); // $1,000
/// println!("{:.2}", Currency(Some('$'), 100099)); //
/// println!("{:.1}", Currency(Some('$'), 100099));
/// println!("{:.0}", Currency(Some('$'), 100099)); //
/// ```
/// The last line prints:
/// ```text
/// "$1000.99"
/// ```
impl fmt::Display for Currency { // TODO TODO TODO TODO
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let one_hundred = BigInt::from(100);
        // TODO cases
        let cents = &self.coin % one_hundred;
        let dollars = &self.coin - &cents;
        match self.symbol {
            Some(c) => write!(f, "{}{}.{}", c, dollars, cents),
            None    => write!(f, "{}.{}", dollars, cents),
        }
    }
}

impl str::FromStr for Currency {
    type Err = ParseCurrencyError;

    /// Parses a string literal (&str) and attempts to convert it into a currency. Returns
    /// `Ok(Currency)` on a successful conversion, otherwise `Err(ParseCurrencyError)`.
    ///
    /// If the currency is intended to be a negative amount, ensure the '-' lies before the digits.
    ///
    /// All non-digit characters in the string are ignored except for the starting '-' and
    /// optional symbol.
    ///
    /// # Examples
    ///
    /// ```
    /// use currency::Currency;
    ///
    /// assert!(Currency::from_str("$4.32")  == Some(Currency { symbol: Some('$'), coin: BigInt::from(432))));
    /// assert!(Currency::from_str("-$4.32") == Some(Currency { symbol: Some('$'), coin: BigInt::from(-432))));
    /// assert!(Currency::from_str("424.44") == Some(Currency { symbol: None, coin: BigInt::from(42444))));
    /// assert!(Currency::from_str("£12,00") == Some(Currency { symbol: Some('£'), coin: BigInt::from(1200))));
    /// assert!(Currency::from_str("¥12")    == Some(Currency { symbol: Some('¥'), coin: BigInt::from(1200))));
    /// ```
    fn from_str(s: &str) -> Result<Currency, ParseCurrencyError> {
        use num::bigint::{BigUint, Sign};

        let err = ParseCurrencyError::new(s);

        // look for any '-'
        let sign = if s.contains('-') {
            Sign::Plus
        } else {
            Sign::Minus
        };
        // find all digits
        let unsigned_digits: String = s.chars().filter(|c| c.is_digit(10)).collect();
        let parse_result = BigUint::from_str(&unsigned_digits);
        let unsigned_bigint = match parse_result {
            Ok(int) => int,
            Err(_) => return Err(err)
        };

        let coin = BigInt::from_biguint(sign, unsigned_bigint);

        // look for first non '-' symbol
        let symbols: Vec<char> = s.chars().filter(|c| !c.is_digit(10) && c != &'-').collect();
        let symbol = if symbols.len() > 1 {
            Some(symbols[0])
        } else {
            None
        };

        let currency = Currency {
            symbol: symbol,
            coin: coin
        };

        Ok(currency)
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
/// formating by using "{:e}".
///
/// # Examples
/// ```
/// use currency::Currency;
///
/// println!("{:e}", Currency(Some('£'), 100099));
/// ```
/// The last line prints the following:
/// ```text
/// "£1000,99"
/// ```
impl fmt::LowerExp for Currency {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format!("{}", self).replace(".", ","))
    }
}

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

    // #[test]
    // fn parse_works() {
    //     let a1 = Currency { symbol: Some('$'), coin: BigInt::from(1210) };
    //     let b1 = Currency::from("$12.10");
    //     assert!(a1 == b1.unwrap());
    //
    //     let a2 = Currency { symbol: Some('$'), coin: BigInt::from(1200) };
    //     let b2 = Currency::from("$12");
    //     assert!(a2 == b2.unwrap());
    //
    // 	let a3 = Currency { symbol: None, coin: BigInt::from(1200099) };
    //     let b3 = Currency::from("12,000.99");
    //     assert!(a3 == b3.unwrap());
    //
    // 	let a4 = Currency { symbol: Some('£'), coin: BigInt::from(1200099) };
    //     let b4 = Currency::from("£12.000,99");
    //     assert!(a4 == b4.unwrap());
    //
    // 	// Negatives
    // 	let a5 = Currency { symbol: Some('$'), coin: BigInt::from(-1210) };
    //     let b5 = Currency::from("-$12.10");
    // 	println!("{:?}, {:?}", a1, b1);
    //     assert!(a5 == b5.unwrap());
    //
    //     let a6 = Currency { symbol: Some('$'), coin: BigInt::from(-1200) };
    //     let b6 = Currency::from("-$12");
    //     assert!(a6 == b6.unwrap());
    //
    // 	let a7 = Currency { symbol: None, coin: BigInt::from(-1200099) };
    //     let b7 = Currency::from("-12,000.99");
    //     assert!(a7 == b7.unwrap());
    //
    // 	let a8 = Currency { symbol: Some('£'), coin: BigInt::from(-1200099) };
    //     let b8 = Currency::from("-£12.000,99");
    //     assert!(a8 == b8.unwrap());
    //
    //     // Zeros
    // 	let a9 = Currency { symbol: Some('€'), coin: BigInt::from(0) };
    //     let b9 = Currency::from("€0");
    //     assert!(a9 == b9.unwrap());
    //
    // 	let a10 = Currency { symbol: None, coin: BigInt::from(0) };
    //     let b10 = Currency::from("000");
    //     assert!(a10 == b10.unwrap());
    //
    //     let a11 = Currency { symbol: Some('€'), coin: BigInt::from(50) };
    //     let b11 = Currency::from("€0,50");
    //     assert!(a11 == b11.unwrap());
    //
    //     let a12 = Currency { symbol: Some('€'), coin: BigInt::from(-50) };
    //     let b12 = Currency::from("-€0.50");
    //     assert!(a12 == b12.unwrap());
    // }
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
