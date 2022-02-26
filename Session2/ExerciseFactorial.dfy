include "ExerciseExp.dfy"

// factorial function
function factorial(n:int):int
requires n >= 0
decreases n {
	if n == 0 then 1 else n * factorial(n-1)
}

// factorial is at least 1
lemma factorialAtLeast1(n:int)
requires n >= 0
ensures factorial(n) >= 1 {}


// factorial is bigger than 3^n
lemma factorialBiggerThanExpLemma(n:int)
requires n >= 7
decreases n
ensures exp(3, n) < factorial(n) {
	if n == 7 {
		assert exp(3, 7) < factorial(7);
	} else {
		factorialBiggerThanExpLemma(n-1);
		factorialAtLeast1(n-1);
		expAtLeast1(3, n-1);
		assert 3 * exp(3, n-1) < n * factorial(n-1);
	}
}

// factorial is smaller than n^n
lemma factorialSmallerThanExpLemma(n:int)
requires n >= 2
decreases n
ensures factorial(n) < exp(n, n) {
	if n == 2 {
		assert factorial(2) < exp(2, 2);
	} else {
		factorialSmallerThanExpLemma(n-1);
		expIncreasing(n-1, n-1); //assume exp(n-1, n-1) <= exp(n, n-1);
		assert n * factorial(n-1) < n * exp(n-1, n-1) <= n * exp(n, n-1);
	}
}
