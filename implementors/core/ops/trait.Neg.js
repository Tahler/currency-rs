(function() {var implementors = {};
implementors['libc'] = [];implementors['num_bigint'] = ["impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num_bigint/struct.BigUint.html' title='num_bigint::BigUint'>BigUint</a>","impl&lt;'a&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num_bigint/struct.BigUint.html' title='num_bigint::BigUint'>BigUint</a>","impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='enum' href='num_bigint/enum.Sign.html' title='num_bigint::Sign'>Sign</a>","impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num_bigint/struct.BigInt.html' title='num_bigint::BigInt'>BigInt</a>","impl&lt;'a&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num_bigint/struct.BigInt.html' title='num_bigint::BigInt'>BigInt</a>",];implementors['num_complex'] = ["impl&lt;T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num_traits/trait.Num.html' title='num_traits::Num'>Num</a> + <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt;&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num_complex/struct.Complex.html' title='num_complex::Complex'>Complex</a>&lt;T&gt;","impl&lt;'a, T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num_traits/trait.Num.html' title='num_traits::Num'>Num</a> + <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt;&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num_complex/struct.Complex.html' title='num_complex::Complex'>Complex</a>&lt;T&gt;",];implementors['num_rational'] = ["impl&lt;T&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num_rational/struct.Ratio.html' title='num_rational::Ratio'>Ratio</a>&lt;T&gt; <span class='where'>where T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num_integer/trait.Integer.html' title='num_integer::Integer'>Integer</a> + <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt;</span>","impl&lt;'a, T&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num_rational/struct.Ratio.html' title='num_rational::Ratio'>Ratio</a>&lt;T&gt; <span class='where'>where T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num_integer/trait.Integer.html' title='num_integer::Integer'>Integer</a> + <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt;</span>",];implementors['num'] = ["impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num/bigint/struct.BigUint.html' title='num::bigint::BigUint'>BigUint</a>","impl&lt;'a&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num/bigint/struct.BigUint.html' title='num::bigint::BigUint'>BigUint</a>","impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='enum' href='num/bigint/enum.Sign.html' title='num::bigint::Sign'>Sign</a>","impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num/bigint/struct.BigInt.html' title='num::bigint::BigInt'>BigInt</a>","impl&lt;'a&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num/bigint/struct.BigInt.html' title='num::bigint::BigInt'>BigInt</a>","impl&lt;T&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num/rational/struct.Ratio.html' title='num::rational::Ratio'>Ratio</a>&lt;T&gt; <span class='where'>where T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num/integer/trait.Integer.html' title='num::integer::Integer'>Integer</a> + <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt;</span>","impl&lt;'a, T&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num/rational/struct.Ratio.html' title='num::rational::Ratio'>Ratio</a>&lt;T&gt; <span class='where'>where T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num/integer/trait.Integer.html' title='num::integer::Integer'>Integer</a> + <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt;</span>","impl&lt;T&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='num/complex/struct.Complex.html' title='num::complex::Complex'>Complex</a>&lt;T&gt; <span class='where'>where T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt; + <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num/traits/trait.Num.html' title='num::traits::Num'>Num</a></span>","impl&lt;'a, T&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='num/complex/struct.Complex.html' title='num::complex::Complex'>Complex</a>&lt;T&gt; <span class='where'>where T: <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a>&lt;Output=T&gt; + <a class='trait' href='https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html' title='core::clone::Clone'>Clone</a> + <a class='trait' href='num/traits/trait.Num.html' title='num::traits::Num'>Num</a></span>",];implementors['currency'] = ["impl <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for <a class='struct' href='currency/struct.Currency.html' title='currency::Currency'>Currency</a>","impl&lt;'a&gt; <a class='trait' href='https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html' title='core::ops::Neg'>Neg</a> for &amp;'a <a class='struct' href='currency/struct.Currency.html' title='currency::Currency'>Currency</a>",];

            if (window.register_implementors) {
                window.register_implementors(implementors);
            } else {
                window.pending_implementors = implementors;
            }
        
})()
