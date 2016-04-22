use std::{ops, cmp, fmt, str, error};

use super::num::bigint::BigInt;
use super::num::Zero;

/// Represents currency through an optional symbol and amount of coin.
///
/// Every 100 coins results in a banknote. (100 is formatted as 1.00)
/// The currency will be formatted as such: `Currency(Some('$'), 432)` ==> "$4.32"
#[derive(Debug, Clone)]
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
    /// ```
    pub fn new() -> Currency {
        Currency {
            symbol: None,
            coin: BigInt::zero()
        }
    }

    // TODO
    // - to_str with comma delimiting
    // - to_str with euro delimiting
}

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

// impl str::FromStr for Currency {
//     type Err = ParseCurrencyError;
//
//     /// Uses a Regular Expression to parse a string literal (&str) and attempts to turn it into a
//     /// currency. Returns `Some(Currency)` on a successful conversion, otherwise `None`.
//     ///
//     /// If the currency is intended to be a negative amount, ensure the '-' is the first character
//     /// in the string.
//     /// The Regex recognizes European notation (€1,00)
//     ///
//     /// # Examples
//     /// ```
//     /// use currency::Currency;
//     ///
//     /// assert!(Currency::from_string("$4.32")  == Some(Currency(Some('$'), 432)));
//     /// assert!(Currency::from_string("-$4.32") == Some(Currency(Some('$'), -432)));
//     /// assert!(Currency::from_string("424.44") == Some(Currency(None, 42444)));
//     /// assert!(Currency::from_string("£12,00") == Some(Currency(Some('£'), 1200)));
//     /// assert!(Currency::from_string("¥12")    == Some(Currency(Some('¥'), 1200)));
//     /// ```
//     fn from_str(s: &str) -> Result<Currency, ParseCurrencyError> {
//         use regex::Regex;
//
//         // Shadow s with a trimmed version
//         let s = s.trim();
//         let re =
//         Regex::new(r"(?:\b|(-)?)(\p{Sc})?((?:(?:\d{1,3}[\.,])+\d{3})|\d+)(?:[\.,](\d{2}))?\b")
//         .unwrap();
//
//         if !re.is_match(s) {
//             return None;
//         }
//
//         // Used to negate the final result if the regex matches a negative
//         let mut multiplier = 1;
//         let mut sign: Option<char> = None;
//         let mut coin_str: String = "".to_string();
//
//         // If anyone's looking at this and knows how to do this without a loop, fork this.
//         for cap in re.captures_iter(s) {
//             if cap.at(0).unwrap_or("") != s {
//                 return None;
//             }
//
//             if cap.at(1).is_some() {
//                 multiplier = -1;
//             }
//
//             if cap.at(2).is_some() {
//                 if multiplier < 0 {
//                     sign = Some(s.chars().skip(1).next().unwrap());
//                 } else {
//                     sign = Some(s.chars().next().unwrap());
//                 }
//             }
//             coin_str = cap.at(3).unwrap().replace(".", "").replace(",", "")
//             + cap.at(4).unwrap_or("00");
//
//             break;
//         }
//
//         if let Ok(coin) = coin_str.parse::<i64>(){
//             return Some(Currency(sign, multiplier * coin));
//         }
//         None
//     }
// }

#[derive(Debug, Clone, PartialEq)]
pub struct ParseCurrencyError {
    source: String
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

/// Overloads the '==' operator for Currency objects.
///
/// # Panics
/// Panics if the two comparators are different types of currency, as denoted by the Currency's
/// symbol.
impl PartialEq<Currency> for Currency {
    fn eq(&self, rhs: &Currency) -> bool {
        self.symbol == rhs.symbol && self.coin == rhs.coin
    }

    fn ne(&self, rhs: &Currency) -> bool {
        self.symbol != rhs.symbol || self.coin != rhs.coin
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
    fn partial_cmp(&self, rhs: &Currency) -> Option<cmp::Ordering> {
        if self.symbol == rhs.symbol {
            self.coin.partial_cmp(&rhs.coin)
        } else {
            None
        }
    }

    fn lt(&self, rhs: &Currency) -> bool {
        if self.symbol == rhs.symbol {
            self.coin.lt(&rhs.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }

    fn le(&self, rhs: &Currency) -> bool {
        if self.symbol == rhs.symbol {
            self.coin.le(&rhs.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }

    fn gt(&self, rhs: &Currency) -> bool {
        if self.symbol == rhs.symbol {
            self.coin.gt(&rhs.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }

    fn ge(&self, rhs: &Currency) -> bool {
        if self.symbol == rhs.symbol {
            self.coin.ge(&rhs.coin)
        } else {
            panic!("Cannot compare two different types of currency.");
        }
    }
}

/// Overloads the '+' operator for Currency objects.
///
/// # Panics
/// Panics if the two addends are different types of currency, as denoted by the Currency's symbol.
impl ops::Add for Currency {
    type Output = Currency;

    fn add(self, rhs: Currency) -> Currency {
        if self.symbol == rhs.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.add(rhs.coin)
            }
        } else {
            panic!("Cannot add two different types of currency.");
        }
    }
}

/// Overloads the '-' operator for Currency objects.
///
/// # Panics
/// Panics if the minuend and subtrahend are two different types of currency, as denoted by the
/// Currency's symbol.
impl ops::Sub for Currency {
    type Output = Currency;

    fn sub(self, rhs: Currency) -> Currency {
        if self.symbol == rhs.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.sub(rhs.coin)
            }
        } else {
            panic!("Cannot subtract two different types of currency.");
        }
    }
}

/// Overloads the '*' operator for Currency objects.
///
/// Allows a Currency to be multiplied by an i64.
impl ops::Mul<i64> for Currency {
    type Output = Currency;

    fn mul(self, rhs: i64) -> Currency {
        Currency {
            symbol: self.symbol,
            coin: self.coin.mul(BigInt::from(rhs))
        }
    }
}
// TODO mul for each num type, both ways

/// Overloads the '*' operator for Currency objects.
///
/// Allows a Currency to be multiplied by an i64.
impl ops::Mul<Currency> for Currency {
    type Output = Currency;

    fn mul(self, rhs: Currency) -> Currency {
        if self.symbol == rhs.symbol {
            Currency {
                symbol: self.symbol,
                coin: self.coin.mul(rhs.coin)
            }
        } else {
            panic!("Cannot multiply two different types of currency.");
        }
    }
}

// TODO
// - neg
// - rem
// - hash
