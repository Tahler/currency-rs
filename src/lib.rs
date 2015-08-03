#![crate_type = "lib"]
#![crate_name = "currency"]

extern crate regex;

use std::cmp::PartialEq;
use std::cmp::PartialOrd;
use std::cmp::Ordering;

use std::ops::Add;
use std::ops::Sub;
use std::ops::Mul;
use std::ops::Div;

use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result;

use std::marker::Copy;

/// Represents currency through an optional symbol and amount of coin.
/// 
/// Each 100 coins results in a banknote. (100 is formatted as 1.00)
/// The currency will be formatted as such:
///     Currency(Some('$'), 432) ==> "$4.32"
#[derive(Debug)]
pub struct Currency(pub Option<char>, pub i64);
 
impl Currency {
    /// Creates a blank Currency as Currency(None, 0)
    /// 
    /// # Examples 
    /// 
    /// ```
	/// use currency::Currency;
	/// 
    /// let mut c = Currency::new();
    /// ```
    #[inline]
    #[allow(dead_code)]
    pub fn new() -> Currency {
        Currency(None, 0)
    }
 
    /// Parses a string literal and turns it into a currency.
    /// 
    /// Parsing ignores spaces and commas, only taking note of the digits and 
    /// leading sign.
    /// 
    /// # Examples
    /// ```
	/// use currency::Currency;
	/// 
    /// assert!(Currency::from_string("$4.32") == Currency(Some('$'), 432));
    /// assert!(Currency::from_string("424.44") == Currency(None, 42444));
    /// assert!(Currency::from_string("@12") == Currency(Some('@'), 1200));
    /// ```
    /// 
    /// # Failures
    /// Fails to take note of the floating points position.
    /// ```
    /// use currency::Currency;
	/// 
    /// assert!(Currency::from_string("$42.012) != Currency(Some('$'), 4201));
    /// assert!(Currency::from_string("42.") != Currency(None, 4200));
    /// ```
    /// 
    /// # Panics
    /// Panics if a number fails to be parsed; this only occurs if the string
    /// argument has no numbers in it.
    ///
    /// # Safety
    /// If a decimal point is intended to be marked, always use '.'
    /// A "European style" ',' will be ignored.
    /// String::from_string("€4.32") instead of String::from_string("€4,32")
    #[allow(dead_code)]
    pub fn from_string(s: &str) -> Currency {
        // Try to find the sign
        let mut sign = None;
        let mut unicode: u8 = s.chars().next().unwrap() as u8;
        // If the first character is not a letter or a decimal point
        if unicode != 0x2E && (unicode < 0x30 || unicode > 0x39) {
            sign = Some(unicode as char);
        }
        
        // Find the numbers
        let mut should_multiply = true; // May later change if '.' is specified
        let mut coin_str = String::new();
        for c in s.chars() {
            unicode = c as u8;
            // Only pay attention to numbers
            if unicode >= 0x30 && unicode <= 0x39 {
                coin_str = coin_str + &c.to_string();
            }
            // If coins are explicitly specified (via a '.'), then we shouldn't
            // multiply at the end
            if unicode == 0x2E {
                should_multiply = false;
            }
        }
        // Parse out the resulting number
        let mut coin: i64 = coin_str.parse()
            .ok()
            .expect("Failed to convert string to currency");
        
        if should_multiply {
            coin *= 100;
        }
        
        // Return result
        Currency(sign, coin)
    }
}
 
/// Overloads the '==' operator for Currency objects.
/// 
/// # Panics
/// Panics if the two comparators are different types of currency, as denoted by
/// the Currency's symbol.
impl PartialEq<Currency> for Currency {
    #[inline]
    fn eq(&self, rhs: &Currency) -> bool {
        self.0 == rhs.0 && self.1 == rhs.1
    }
 
    #[inline]
    fn ne(&self, rhs: &Currency) -> bool {
        self.0 != rhs.0 || self.1 != rhs.1
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
    #[inline]
    fn partial_cmp(&self, rhs: &Currency) -> Option<Ordering> {
        if self.0 == rhs.0 {
            if self < rhs { return Some(Ordering::Less) }
            if self == rhs { return Some(Ordering::Equal) }
            if self > rhs { return Some(Ordering::Greater) }
        }
        None
    }
    
    #[inline]
    fn lt(&self, rhs: &Currency) -> bool {
        if self.0 == rhs.0 { 
            self.1 < rhs.1 
        }
        else { 
            panic!("Cannot compare two different types of currency."); 
        }
    }
    #[inline]
    fn le(&self, rhs: &Currency) -> bool {
        self < rhs || self == rhs
    }
    #[inline]
    fn gt(&self, rhs: &Currency) -> bool {
        if self.0 == rhs.0 { 
            self.1 > rhs.1 
        }
        else { 
            panic!("Cannot compare two different types of currency."); 
        }
    }
    #[inline]
    fn ge(&self, rhs: &Currency) -> bool {
        self > rhs || self == rhs
    }
}
 
/// Overloads the '+' operator for Currency objects.
/// 
/// # Panics
/// Panics if the two addends are different types of currency, as denoted by the
/// Currency's symbol.
impl Add for Currency {
    type Output = Currency;
 
    #[inline]
    fn add(self, rhs: Currency) -> Currency {
        if self.0 == rhs.0 {
            Currency(self.0, self.1 + rhs.1)
        } else {
            panic!("Cannot add two different types of currency!");
        }
    }
}
 
/// Overloads the '-' operator for Currency objects.
/// 
/// # Panics
/// Panics if the minuend and subtrahend are two different types of currency, 
/// as denoted by the Currency's symbol.
impl Sub for Currency {
    type Output = Currency;
    
    #[inline]
    fn sub(self, rhs: Currency) -> Currency {
        if self.0 == rhs.0 {
            Currency(self.0, self.1 - rhs.1)
        } else {
            panic!("Cannot subtract two different types of currency!");
        }
    }
}
 
/// Overloads the '*' operator for Currency objects.
///
/// Allows a Currency to be multiplied by an i64.
impl Mul<i64> for Currency {
    type Output = Currency;
    
    #[inline]
    fn mul(self, rhs: i64) -> Currency {
        Currency(self.0, self.1 * rhs)
    }
}
 
/// Overloads the '*' operator for i64.
/// 
/// Allows an i64 to be multiplied by a Currency.
/// Completes the commutative property for i64 multiplied by Currency.
impl Mul<Currency> for i64 {
    type Output = Currency;
    
    #[inline]
    fn mul(self, rhs: Currency) -> Currency {
        Currency(rhs.0, rhs.1 * self)
    }
}
 
/// Overloads the '/' operator for Currency objects.
/// 
/// Allows a Currency to be divided by an i64.
impl Div<i64> for Currency {
    type Output = Currency;
    
    #[inline]
    fn div(self, rhs: i64) -> Currency {
        Currency(self.0, self.1 / rhs)
    }
}
 
/// Allows Currencies to be displayed as Strings
/// 
/// # Examples
/// ```
/// use currency::Currency;
/// 
/// assert!(Currency(Some('$'), 1210).to_string() == "$12.10");
/// assert!(Currency(None, 1210).to_string() == "12.10");
/// ```
impl Display for Currency {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> Result {
        let decimal = (self.1 / 100).to_string()
            + &('.').to_string()
            + &(self.1 % 100).to_string();
        match self.0 {
            Some(c) => write!(f, "{}{}", c, decimal),
            None    => write!(f, "{}", decimal),
        }
    }
}
 
/// Allows Currencies to be copied, rather than using move semantics.
impl Copy for Currency { }
impl Clone for Currency {
    #[inline]
    fn clone(&self) -> Currency { *self }
}
 

