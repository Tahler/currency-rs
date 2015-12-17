extern crate currency;

use currency::Currency;
use std::cmp::Ordering;

#[test]
fn parsing(){
    // all these should pass in the end
    assert_eq!(Currency::from_string("€0,50"),  Some(Currency(Some('€'), 50)));
    assert_eq!(Currency::from_string("€0.50"),  Some(Currency(Some('€'), 50)));
    assert_eq!(Currency::from_string("-€0.50"),  Some(Currency(Some('€'), -50)));
    //assert_eq!(Currency::from_string("€-0.50"),  Some(Currency(Some('€'), -50)));
    //assert_eq!(Currency::from_string("x0.50"),  Some(Currency(Some('x'), 50)));
    //assert_eq!(Currency::from_string("0.50x"),  Some(Currency(Some('x'), 50)));
    //assert_eq!(Currency::from_string("0.5"),  Some(Currency(None, 50)));
    //assert_eq!(Currency::from_string(".5"),   Some(Currency(None, 50)));
    //assert_eq!(Currency::from_string(".55"),  Some(Currency(None, 55)));
    //assert_eq!(Currency::from_string(".559"), None);

}

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
    let a = Currency(Some('$'), 1210);
    let b = Currency::from_string("$12.10");
    assert!(Some(a) == b);

    let c = Currency(Some('$'), 1200);
    let d = Currency::from_string("$12");
    assert!(Some(c) == d);

	let e = Currency(None, 1200099);
    let f = Currency::from_string("12,000.99");
    assert!(Some(e) == f);

	let g = Currency(Some('£'), 1200099);
    let h = Currency::from_string("£12.000,99");
    assert!(Some(g) == h);

	// Negatives
	let a1 = Currency(Some('$'), -1210);
    let b1 = Currency::from_string("-$12.10");
	println!("{:?}, {:?}", a1, b1);
    assert!(Some(a1) == b1);

    let c1 = Currency(Some('$'), -1200);
    let d1 = Currency::from_string("-$12");
    assert!(Some(c1) == d1);

	let e1 = Currency(None, -1200099);
    let f1 = Currency::from_string("-12,000.99");
    assert!(Some(e1) == f1);

	let g1 = Currency(Some('£'), -1200099);
    let h1 = Currency::from_string("-£12.000,99");
    assert!(Some(g1) == h1);
}

#[test]
fn display_works() {
	assert!(format!("{:?}", Currency(None, 10)) == "Currency(None, 10)");

	assert!(Currency(None, 1210).to_string() == "12.10");
    assert!(Currency(Some('$'), 1210).to_string() == "$12.10");
    assert!(Currency(Some('$'), 100010).to_string() == "$1000.10");

	assert!(format!("{:e}", Currency(Some('£'), 100000)) == "£1000,00");
}
