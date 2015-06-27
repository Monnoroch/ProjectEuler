#![feature(step_by)]
#![feature(collections)]
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
	pub struct EratosfenPrimeGenerator {
		primes: Vec<u64>,
		current: u64,
		inc: u64,
	}

	impl EratosfenPrimeGenerator {
		pub fn new() -> EratosfenPrimeGenerator {
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

	pub struct EratosfenPrimeGeneratorBelowN {
		primes: Vec<u64>,
		cur: usize,
	}

	impl EratosfenPrimeGeneratorBelowN {
		pub fn new(num: usize) -> EratosfenPrimeGeneratorBelowN {
			let mut primes = Vec::new();
			let mut numbers = Vec::with_capacity(num);
			for _ in 0..num {
				numbers.push(true);
			}
			for n in 2..num {
				let mut stop = true;
				for i in (n*2..num).step_by(n) {
					// println!("numbers[{:?}] = false", i);
					numbers[i] = false;
					stop = false;
				}
				if stop {
					break;
				}
			}
			for (n, v) in numbers.iter().cloned().enumerate() {
				if n >= 2 && v {
					primes.push(n as u64);
				}
			}

			EratosfenPrimeGeneratorBelowN{
				primes: primes,
				cur: 0,
			}
		}
	}

	impl Iterator for EratosfenPrimeGeneratorBelowN {
		type Item = u64;

		fn next(&mut self) -> Option<Self::Item> {
			let idx = self.cur;
			self.cur += 1;
			if idx >= self.primes.len() {
				None
			} else {
				Some(self.primes[idx])
			}
		}
	}

	fn nth_prime(num: usize) -> u64 {
		EratosfenPrimeGenerator::new().nth(num).unwrap()
	}

	fn nth_prime_from_one(num: usize) -> u64 {
		nth_prime(num - 1)
	}

	#[test]
	fn test_primes() {
		for (p1, p2) in EratosfenPrimeGenerator::new().zip(EratosfenPrimeGeneratorBelowN::new(100000)).take(1000) {
			assert_eq!(p1, p2);
		}
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

mod task10 {
	use task7::EratosfenPrimeGeneratorBelowN;

	fn sum_primes_below(num: usize) -> u64 {
		let mut sum = 0;
		for p in EratosfenPrimeGeneratorBelowN::new(num) {
			sum += p;
		}
		sum
	}

	#[test]
	fn test() {
		assert_eq!(sum_primes_below(2000000), 142913828922);
	}
}

mod task11 {
	use std::cmp::max;

	fn largest_seq_product_of_n_digits(grid: &Vec<Vec<u64>>, num: usize) -> u64 {
		let mut max_product = 0;
		// rows
		for v in grid {
			for i in (num - 1)..v.len() {
				let mut product = 1u64;
				for j in 0..num {
					product *= v[i - j];
				}
				max_product = max(max_product, product);
			}
		}

		// columns
		for n in 0..grid[0].len() {
			for i in (num - 1)..grid.len() {
				let mut product = 1u64;
				for j in 0..num {
					product *= grid[i - j][n];
				}
				max_product = max(max_product, product);
			}
		}

		// lower half left->right (+ diagonal)
		for i in 0..grid.len() {
			for n in (num - 1)..grid.len() {
				if i + n >= grid.len() {
					break;
				}

				let mut product = 1u64;
				for j in 0..num {
					product *= grid[(i + n) - j][n - j];
				}
				max_product = max(max_product, product);
			}
		}

		// upper half left->right
		for i in 1..grid.len() {
			for n in (num - 1)..grid.len() {
				if i + n >= grid.len() {
					break;
				}

				let mut product = 1u64;
				for j in 0..num {
					product *= grid[n - j][(i + n) - j];
				}
				max_product = max(max_product, product);
			}
		}

		// lower half right->left (+ diagonal)
		for i in 0..grid.len() {
			for n in (num - 1)..grid.len() {
				if i + n >= grid.len() {
					break;
				}

				let mut product = 1u64;
				for j in 0..num {
					product *= grid[(i + n) - j][(grid.len() + j) - n - 1];
				}
				max_product = max(max_product, product);
			}
		}

		// upper half right->left
		for i in (0..(grid.len() - 1)).rev() {
			for n in (num - 1)..grid.len() {
				if i < n {
					break;
				}

				let mut product = 1u64;
				for j in 0..num {
					product *= grid[n - j][(i + j) - n];
				}
				max_product = max(max_product, product);
			}
		}

		max_product
	}

	#[test]
	fn test() {
		assert_eq!(
			largest_seq_product_of_n_digits(
				&vec![
					vec![08u64, 02, 22, 97, 38, 15, 00, 40, 00, 75, 04, 05, 07, 78, 52, 12, 50, 77, 91, 08],
					vec![49, 49, 99, 40, 17, 81, 18, 57, 60, 87, 17, 40, 98, 43, 69, 48, 04, 56, 62, 00],
					vec![81, 49, 31, 73, 55, 79, 14, 29, 93, 71, 40, 67, 53, 88, 30, 03, 49, 13, 36, 65],
					vec![52, 70, 95, 23, 04, 60, 11, 42, 69, 24, 68, 56, 01, 32, 56, 71, 37, 02, 36, 91],
					vec![22, 31, 16, 71, 51, 67, 63, 89, 41, 92, 36, 54, 22, 40, 40, 28, 66, 33, 13, 80],
					vec![24, 47, 32, 60, 99, 03, 45, 02, 44, 75, 33, 53, 78, 36, 84, 20, 35, 17, 12, 50],
					vec![32, 98, 81, 28, 64, 23, 67, 10, 26, 38, 40, 67, 59, 54, 70, 66, 18, 38, 64, 70],
					vec![67, 26, 20, 68, 02, 62, 12, 20, 95, 63, 94, 39, 63, 08, 40, 91, 66, 49, 94, 21],
					vec![24, 55, 58, 05, 66, 73, 99, 26, 97, 17, 78, 78, 96, 83, 14, 88, 34, 89, 63, 72],
					vec![21, 36, 23, 09, 75, 00, 76, 44, 20, 45, 35, 14, 00, 61, 33, 97, 34, 31, 33, 95],
					vec![78, 17, 53, 28, 22, 75, 31, 67, 15, 94, 03, 80, 04, 62, 16, 14, 09, 53, 56, 92],
					vec![16, 39, 05, 42, 96, 35, 31, 47, 55, 58, 88, 24, 00, 17, 54, 24, 36, 29, 85, 57],
					vec![86, 56, 00, 48, 35, 71, 89, 07, 05, 44, 44, 37, 44, 60, 21, 58, 51, 54, 17, 58],
					vec![19, 80, 81, 68, 05, 94, 47, 69, 28, 73, 92, 13, 86, 52, 17, 77, 04, 89, 55, 40],
					vec![04, 52, 08, 83, 97, 35, 99, 16, 07, 97, 57, 32, 16, 26, 26, 79, 33, 27, 98, 66],
					vec![88, 36, 68, 87, 57, 62, 20, 72, 03, 46, 33, 67, 46, 55, 12, 32, 63, 93, 53, 69],
					vec![04, 42, 16, 73, 38, 25, 39, 11, 24, 94, 72, 18, 08, 46, 29, 32, 40, 62, 76, 36],
					vec![20, 69, 36, 41, 72, 30, 23, 88, 34, 62, 99, 69, 82, 67, 59, 85, 74, 04, 36, 16],
					vec![20, 73, 35, 29, 78, 31, 90, 01, 74, 31, 49, 71, 48, 86, 81, 16, 23, 57, 05, 54],
					vec![01, 70, 54, 71, 83, 51, 54, 69, 16, 92, 33, 48, 61, 43, 52, 01, 89, 19, 67, 48],
				],
				4
			),
			70600674
		);
	}
}

mod task12 {
	use std::collections::BitVec;
	use std::collections::HashSet;
	use task3::factorize;

	fn inc(num: &mut BitVec) -> bool {
		for i in 0..num.len() {
			if num[i] {
				num.set(i, false);
			} else {
				num.set(i, true);
				return true;
			}
		}
		return false;
	}

	fn divisors_count(num: u64) -> usize {
		let factors = factorize(num);
		let mut bv = BitVec::from_elem(factors.len(), false);
		let mut divisors = HashSet::new();
		while inc(&mut bv) {
			let mut product = 1;
			for i in 0..bv.len() {
				if bv[i] {
					product *= factors[i];
				}
			}
			divisors.insert(product);
		}
		divisors.len() + 2
	}

	fn first_triangle_over_n_divisors(num: usize) -> u64 {
		let mut sum = 0;
		for i in 1.. {
			sum += i;
			if divisors_count(sum) > num {
				return sum;
			}
		}
		unreachable!();
	}

	#[test]
	fn test() {
		assert_eq!(first_triangle_over_n_divisors(500), 76576500);
	}
}
