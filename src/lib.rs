#![allow(dead_code)]

mod task1 {
	fn sum_multiples_3_or_5_below(below: u64) -> u64 {
		let mut s = 0;
		for i in 1..below {
			if i % 5 == 0 || i % 3 == 0 {
				s += i;
			}
		}
		s
	}

	#[test]
	fn test() {
		assert_eq!(sum_multiples_3_or_5_below(1000), 233168);
	}
}

mod task2 {
	fn sum_even_fibs_below(below: u64) -> u64 {
		let mut s = 0;
		let mut v1;
		let mut v2 = 1;
		let mut val = 1;
		while val <= below {
			if val % 2 == 0 {
				s += val;
			}
			v1 = v2;
			v2 = val;
			val = v1 + v2;
		}
		s
	}

	#[test]
	fn test() {
		assert_eq!(sum_even_fibs_below(4000000), 4613732);
	}
}

mod task3 {
	pub fn factorize(num: u64) -> Vec<u64> {
		let mut n = num;
		let mut factor = 2u64;
		let mut factors = vec![];
		while n > 1 && factor.pow(2) <= n {
			while n % factor == 0 {
				factors.push(factor);
				n /= factor;
			}
			factor += 1;
		}
		factors.push(n);
		factors
	}

	fn largest_factor(num: u64) -> u64 {
		*factorize(num).iter().max().unwrap()
	}

	#[test]
	fn test() {
		assert_eq!(largest_factor(600851475143), 6857);
	}
}

mod task4 {
	fn is_palindrome(num: u64) -> bool {
		let s = num.to_string().into_bytes();
		let l = s.len();
		for i in 0..l/2 {
			if s[i] != s[l - i - 1] {
				return false;
			}
		}
		true
	}

	fn largest_palindrome_product(digits: u32) -> u64 {
		let min = 10u64.pow(digits - 1);
		let max = 10u64.pow(digits) - 1;
		let mut res = vec![];
		for i in (min..max).rev() {
			for j in (min..max).rev() {
				if is_palindrome(i * j) {
					res.push(i * j);
				}
			}
		}
		*res.iter().max().unwrap()
	}

	#[test]
	fn test() {
		assert_eq!(largest_palindrome_product(3), 906609);
	}
}
