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

mod task5 {
	use std::cmp::max;
	use std::collections::HashMap;
	use task3;

	fn factorize_map(num: u64) -> HashMap<u64, u64> {
		let mut map = HashMap::new();
		for f in task3::factorize(num) {
			let counter = map.entry(f).or_insert(0);
			*counter += 1;
		}
		map
	}

	fn smallest_multimle_of_all_up_to(num: u64) -> u64 {
		let mut all_map: HashMap<u64, u32> = HashMap::new();
		for i in (2..(num + 1)).rev() {
			for (k, v) in &factorize_map(i) {
				let counter = all_map.entry(*k).or_insert(*v as u32);
				*counter = max(*v as u32, *counter);
			}
		}
		let mut res = 1u64;
		for (k, v) in &all_map {
			res *= k.pow(*v);
		}
		res
	}


	#[test]
	fn test() {
		assert_eq!(smallest_multimle_of_all_up_to(20), 232792560);
	}
}

mod task6 {
	fn square_sum_minus_sum_squares_up_to(num: u64) -> u64 {
		let mut s = 0u64;
		let mut ss = 0u64;
		for x in 1..(num + 1) {
			s += x.pow(2);
			ss += x;
		}
		ss.pow(2) - s
	}


	#[test]
	fn test() {
		assert_eq!(square_sum_minus_sum_squares_up_to(100), 25164150);
	}
}
