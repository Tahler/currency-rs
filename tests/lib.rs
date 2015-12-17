extern crate currency;

use currency::Currency;
use std::cmp::Ordering;

#[test]
fn eq_works() {
    let a = Currency(Some('$'), 1210);
    let b = Currency(Some('$'), 1210);
    let c = Currency(Some('$'), 1251);

    assert!(a == b);
    assert!(b == b);
    assert!(b == a);
    assert!(a != c);
}

#[test]
fn ord_works() {
    let a = Currency(Some('$'), 1210);
    let b = Currency(Some('$'), 1211);
    let c = Currency(Some('$'), 1311);
    let d = Currency(Some('$'), 1210);

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
fn arithmetic_works() {
    let x = Currency(Some('$'), 1206);
    let y = Currency(Some('$'), 1143);

    assert!(x + y == Currency(Some('$'), 2349)
         && y + x == Currency(Some('$'), 2349));
    assert!(x - y == Currency(Some('$'), 63));
    assert!(y - x == Currency(Some('$'), -63));
    assert!(x * 2 == Currency(Some('$'), 2412)
         && 2 * x == Currency(Some('$'), 2412));
    assert!(x / 2 == Currency(Some('$'), 603));
}

#[test]
fn parse_works() {
    let a1 = Currency(Some('$'), 1210);
    let b1 = Currency::from_string("$12.10");
    assert!(a1 == b1.unwrap());

    let a2 = Currency(Some('$'), 1200);
    let b2 = Currency::from_string("$12");
    assert!(a2 == b2.unwrap());

	let a3 = Currency(None, 1200099);
    let b3 = Currency::from_string("12,000.99");
    assert!(a3 == b3.unwrap());

	let a4 = Currency(Some('£'), 1200099);
    let b4 = Currency::from_string("£12.000,99");
    assert!(a4 == b4.unwrap());

	// Negatives
	let a5 = Currency(Some('$'), -1210);
    let b5 = Currency::from_string("-$12.10");
	println!("{:?}, {:?}", a1, b1);
    assert!(a5 == b5.unwrap());

    let a6 = Currency(Some('$'), -1200);
    let b6 = Currency::from_string("-$12");
    assert!(a6 == b6.unwrap());

	let a7 = Currency(None, -1200099);
    let b7 = Currency::from_string("-12,000.99");
    assert!(a7 == b7.unwrap());

	let a8 = Currency(Some('£'), -1200099);
    let b8 = Currency::from_string("-£12.000,99");
    assert!(a8 == b8.unwrap());
    
    // Zeros
	let a9 = Currency(Some('€'), 0);
    let b9 = Currency::from_string("€0");
    assert!(a9 == b9.unwrap());

	let a10 = Currency(None, 0);
    let b10 = Currency::from_string("000");
    assert!(a10 == b10.unwrap());
    
    let a11 = Currency(Some('€'), 50);
    let b11 = Currency::from_string("€0,50");
    assert!(a11 == b11.unwrap());

    let a12 = Currency(Some('€'), -50);
    let b12 = Currency::from_string("-€0.50");
    assert!(a12 == b12.unwrap());
}

#[test]
fn display_works() {
	assert!(format!("{:?}", Currency(None, 10)) == "Currency(None, 10)");

	assert!(Currency(None, 1210).to_string() == "12.10");
    assert!(Currency(Some('$'), 1210).to_string() == "$12.10");
    assert!(Currency(Some('$'), 100010).to_string() == "$1000.10");

	assert!(format!("{:e}", Currency(Some('£'), 100000)) == "£1000,00");
}
