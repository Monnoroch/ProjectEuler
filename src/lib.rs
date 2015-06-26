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

mod task7 {
	struct EratosfenPrimeGenerator {
		primes: Vec<u64>,
		current: u64,
		inc: u64,
	}

	impl EratosfenPrimeGenerator {
		fn new() -> EratosfenPrimeGenerator {
			EratosfenPrimeGenerator{
				primes: Vec::new(),
				current: 2,
				inc: 1,
			}
		}
	}

	impl Iterator for EratosfenPrimeGenerator {
		type Item = u64;

		fn next(&mut self) -> Option<Self::Item> {
			let res = self.current;
			loop {
				self.current += self.inc;
				self.inc = 2;
				if !self.primes.iter().any(|p| self.current % p == 0) {
					self.primes.push(self.current);
					break;
				}
			}
			Some(res)
		}
	}

	fn nth_prime(num: usize) -> u64 {
		EratosfenPrimeGenerator::new().nth(num).unwrap()
	}

	fn nth_prime_from_one(num: usize) -> u64 {
		nth_prime(num - 1)
	}


	#[test]
	fn test() {
		assert_eq!(nth_prime_from_one(10001), 104743);
	}
}

mod task8 {
	use std::cmp::max;

	fn largest_seq_product_of_n_digits(seq: &str, num: usize) -> u64 {
		let mut digits = seq.to_string().into_bytes();
		for d in &mut digits {
			*d -= '0' as u8;
		}

		let mut max_product = 1;
		for v in digits.iter().take(num) {
			max_product *= *v as u64;
		}

		for (i, _) in digits.iter().enumerate().skip(num) {
			let mut product = 1;
			for n in 0..num {
				product *= digits[i - n] as u64;
			}
			max_product = max(max_product, product);
		}
		max_product
	}

	#[test]
	fn test() {
		assert_eq!(
			largest_seq_product_of_n_digits(
				"7316717653133062491922511967442657474235534919493496983520312774506326239578318016984801869478851843858615607891129494954595017379583319528532088055111254069874715852386305071569329096329522744304355766896648950445244523161731856403098711121722383113622298934233803081353362766142828064444866452387493035890729629049156044077239071381051585930796086670172427121883998797908792274921901699720888093776657273330010533678812202354218097512545405947522435258490771167055601360483958644670632441572215539753697817977846174064955149290862569321978468622482839722413756570560574902614079729686524145351004748216637048440319989000889524345065854122758866688116427171479924442928230863465674813919123162824586178664583591245665294765456828489128831426076900422421902267105562632111110937054421750694165896040807198403850962455444362981230987879927244284909188845801561660979191338754992005240636899125607176060588611646710940507754100225698315520005593572972571636269561882670428252483600823257530420752963450",
				13
			),
			23514624000
		);
	}
}

mod task9 {
	fn product_pithagorean_triples_when_sum_is_1000() -> u64 {
		for a in 1..999 {
			for b in 1..(999 - a) {
				let sum = a + b;
				let val = a*a + b*b;
				for c in 1..999 { // will only make some iterations, so no need to optimize
					if val == c * c && sum + c == 1000  {
						return a * b * c;
					}
				}
			}
		}
		unreachable!();
	}

	#[test]
	fn test() {
		assert_eq!(product_pithagorean_triples_when_sum_is_1000(), 31875000);
	}
}
