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
 
    /// Uses a Regular Expression to parse a string literal (&str) and turns it into a currency.
    /// 
    /// The Regex recognizes European notation (€1,00)
	/// The display method will print out the format with no comma delimiting with decimal($1000.00)
    /// 
    /// # Examples
    /// ```
	/// use currency::Currency;
	/// 
    /// assert!(Currency::from_string("$4.32") == Currency(Some('$'), 432));
    /// assert!(Currency::from_string("424.44") == Currency(None, 42444));
	/// assert!(Currency::from_string("£12,00") == Currency(Some('£'), 1200));
	/// assert!(Currency::from_string("¥12") == Currency(Some('¥'), 1200));
    /// ```
    /// 
    /// # Failures
    /// Fails if the string is not formatted correctly.
	/// Fails to parse negative money.
    /// 
    /// # Panics
    /// Panics if a number fails to be parsed; this only occurs if the string
    /// argument has no numbers in it.
    #[allow(dead_code)]
    pub fn from_string(s: &str) -> Currency {
		use regex::Regex;
	
		// Shadow s with a trimmed version
		let s = s.trim();
		let re = Regex::new(r"(?:\b|(\p{Sc})?)((?:(?:\d{1,3}[\.,])+\d{3})|\d+)(?:[\.,](\d{2}))?\b").unwrap();
		
		if !re.is_match(s) {
			panic!("Failed to convert \"{}\" to currency", s);
		}
		
		let mut sign: Option<char> = None;
		let mut coin_str: String = "".to_string();
		
		// If anyone's looking at this and knows how to do this without a loop, fork this.
		for cap in re.captures_iter(s) {
			// Without this, there is undefined behavior (try putting a character in the middle of s)
			if cap.at(0).unwrap_or("") != s {
				panic!("Failed to convert \"{}\" to currency", s);
			}
			
			if cap.at(1).is_some() {
				sign = Some(s.chars().next().unwrap());
			}
			coin_str = cap.at(2).unwrap().replace(".", "").replace(",", "") + cap.at(3).unwrap_or("00");
			
			break;
		}
		
		let coin: i64 = coin_str.parse::<i64>().ok().unwrap();
		
		Currency(sign, coin)
	}
}

/// Allows Currencies to be displayed as Strings
/// println!("{}", Currency(Some('$'), 1099)) -> "$10.99"
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
		let decimal = format!("{:.*}", 2, (self.1 as f32 / 100.0));
        match self.0 {
            Some(c) => write!(f, "{}{}", c, decimal),
            None    => write!(f, "{}", decimal),
        }
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
 
/// Allows Currencies to be copied, rather than using move semantics.
impl Copy for Currency { }
impl Clone for Currency {
    #[inline]
    fn clone(&self) -> Currency { *self }
}
 

