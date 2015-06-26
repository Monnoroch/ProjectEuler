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
