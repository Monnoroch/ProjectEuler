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
	struct FibonacciSequence {
		v1: u64,
		v2: u64,
	}

	impl FibonacciSequence {
		fn new() -> FibonacciSequence {
			FibonacciSequence{
				v1: 0,
				v2: 1,
			}
		}
	}

	impl Iterator for FibonacciSequence {
		type Item = u64;

		fn next(&mut self) -> Option<Self::Item> {
			let res = self.v2 + self.v1;
			self.v1 = self.v2;
			self.v2 = res;
			Some(res)
		}
	}

	fn sum_even_fibs_below(below: u64) -> u64 {
		let mut sum = 0;
		for v in FibonacciSequence::new() {
			if v > below {
				break;
			}

			if v % 2 == 0 {
				sum += v;
			}
		}
		sum
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

/*
Solution to this problem is hacky.
Since even the lowest digit can influence the value of a highest digits when summing,
the correct way to do this is to sum long numbers and just obtain 10 highest digits.
But I assumed, that the task coiuld be solved without implementing long summation,
and therefore lowest digits in fact do not influence the value of highest digits,
so I just took as much high digits as I could (19 [digits in u64] - log10(100 [numbers])) frim each number,
added them up and took 10 highest digits from the sum.
*/
mod task13 {
	use std::str::FromStr;

	fn first_10_digits_of_sum(nums: &Vec<&str>) -> u64 {
		let mut sum = 0u64;
		for n in nums {
			sum += <u64 as FromStr>::from_str(&n[0..17]).ok().unwrap();
		}
		let max = 10u64.pow(10) - 1;
		while sum > max {
			sum /= 10;
		}
		sum
	}

	#[test]
	fn test() {
		assert_eq!(
			first_10_digits_of_sum(&vec![
				"37107287533902102798797998220837590246510135740250",
				"46376937677490009712648124896970078050417018260538",
				"74324986199524741059474233309513058123726617309629",
				"91942213363574161572522430563301811072406154908250",
				"23067588207539346171171980310421047513778063246676",
				"89261670696623633820136378418383684178734361726757",
				"28112879812849979408065481931592621691275889832738",
				"44274228917432520321923589422876796487670272189318",
				"47451445736001306439091167216856844588711603153276",
				"70386486105843025439939619828917593665686757934951",
				"62176457141856560629502157223196586755079324193331",
				"64906352462741904929101432445813822663347944758178",
				"92575867718337217661963751590579239728245598838407",
				"58203565325359399008402633568948830189458628227828",
				"80181199384826282014278194139940567587151170094390",
				"35398664372827112653829987240784473053190104293586",
				"86515506006295864861532075273371959191420517255829",
				"71693888707715466499115593487603532921714970056938",
				"54370070576826684624621495650076471787294438377604",
				"53282654108756828443191190634694037855217779295145",
				"36123272525000296071075082563815656710885258350721",
				"45876576172410976447339110607218265236877223636045",
				"17423706905851860660448207621209813287860733969412",
				"81142660418086830619328460811191061556940512689692",
				"51934325451728388641918047049293215058642563049483",
				"62467221648435076201727918039944693004732956340691",
				"15732444386908125794514089057706229429197107928209",
				"55037687525678773091862540744969844508330393682126",
				"18336384825330154686196124348767681297534375946515",
				"80386287592878490201521685554828717201219257766954",
				"78182833757993103614740356856449095527097864797581",
				"16726320100436897842553539920931837441497806860984",
				"48403098129077791799088218795327364475675590848030",
				"87086987551392711854517078544161852424320693150332",
				"59959406895756536782107074926966537676326235447210",
				"69793950679652694742597709739166693763042633987085",
				"41052684708299085211399427365734116182760315001271",
				"65378607361501080857009149939512557028198746004375",
				"35829035317434717326932123578154982629742552737307",
				"94953759765105305946966067683156574377167401875275",
				"88902802571733229619176668713819931811048770190271",
				"25267680276078003013678680992525463401061632866526",
				"36270218540497705585629946580636237993140746255962",
				"24074486908231174977792365466257246923322810917141",
				"91430288197103288597806669760892938638285025333403",
				"34413065578016127815921815005561868836468420090470",
				"23053081172816430487623791969842487255036638784583",
				"11487696932154902810424020138335124462181441773470",
				"63783299490636259666498587618221225225512486764533",
				"67720186971698544312419572409913959008952310058822",
				"95548255300263520781532296796249481641953868218774",
				"76085327132285723110424803456124867697064507995236",
				"37774242535411291684276865538926205024910326572967",
				"23701913275725675285653248258265463092207058596522",
				"29798860272258331913126375147341994889534765745501",
				"18495701454879288984856827726077713721403798879715",
				"38298203783031473527721580348144513491373226651381",
				"34829543829199918180278916522431027392251122869539",
				"40957953066405232632538044100059654939159879593635",
				"29746152185502371307642255121183693803580388584903",
				"41698116222072977186158236678424689157993532961922",
				"62467957194401269043877107275048102390895523597457",
				"23189706772547915061505504953922979530901129967519",
				"86188088225875314529584099251203829009407770775672",
				"11306739708304724483816533873502340845647058077308",
				"82959174767140363198008187129011875491310547126581",
				"97623331044818386269515456334926366572897563400500",
				"42846280183517070527831839425882145521227251250327",
				"55121603546981200581762165212827652751691296897789",
				"32238195734329339946437501907836945765883352399886",
				"75506164965184775180738168837861091527357929701337",
				"62177842752192623401942399639168044983993173312731",
				"32924185707147349566916674687634660915035914677504",
				"99518671430235219628894890102423325116913619626622",
				"73267460800591547471830798392868535206946944540724",
				"76841822524674417161514036427982273348055556214818",
				"97142617910342598647204516893989422179826088076852",
				"87783646182799346313767754307809363333018982642090",
				"10848802521674670883215120185883543223812876952786",
				"71329612474782464538636993009049310363619763878039",
				"62184073572399794223406235393808339651327408011116",
				"66627891981488087797941876876144230030984490851411",
				"60661826293682836764744779239180335110989069790714",
				"85786944089552990653640447425576083659976645795096",
				"66024396409905389607120198219976047599490197230297",
				"64913982680032973156037120041377903785566085089252",
				"16730939319872750275468906903707539413042652315011",
				"94809377245048795150954100921645863754710598436791",
				"78639167021187492431995700641917969777599028300699",
				"15368713711936614952811305876380278410754449733078",
				"40789923115535562561142322423255033685442488917353",
				"44889911501440648020369068063960672322193204149535",
				"41503128880339536053299340368006977710650566631954",
				"81234880673210146739058568557934581403627822703280",
				"82616570773948327592232845941706525094512325230608",
				"22918802058777319719839450180888072429661980811197",
				"77158542502016545090413245809786882778948721859617",
				"72107838435069186155435662884062257473692284509516",
				"20849603980134001723930671666823555245252804609722",
				"53503534226472524250874054075591789781264330331690",
			]),
			5537376230
		);
	}
}

mod task14 {
	struct CollatzSequence {
		current: u64,
		stop: bool,
	}

	impl CollatzSequence {
		fn from(start: u64) -> CollatzSequence {
			CollatzSequence{
				current: start,
				stop: false,
			}
		}
	}

	impl Iterator for CollatzSequence {
		type Item = u64;

		fn next(&mut self) -> Option<Self::Item> {
			if self.stop {
				return None;
			}

			let res = self.current;
			if res % 2 == 0 {
				self.current /= 2;
			} else {
				if res == 1 {
					self.stop = true;
				} else {
					self.current = res * 3 + 1;
				}
			}
			Some(res)
		}
	}

	fn longest_collatz_start(below: u64) -> u64 {
		let mut max_val = 0;
		let mut max_cnt = 0;
		for i in 2..below {
			let cnt = CollatzSequence::from(i).count();
			if cnt > max_cnt {
				max_cnt = cnt;
				max_val = i;
			}
		}
		max_val
	}

	#[test]
	fn test() {
		assert_eq!(longest_collatz_start(1000000), 837799);
	}
}
