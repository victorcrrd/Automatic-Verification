function exp(b:int, e:int):int
requires e >= 0
decreases e {
  if e == 0 then 1 else b * exp(b, e-1)
}

function factorial(n:int):(f:int)
requires n >= 0
ensures f >= 1
decreases n {
  if n == 0 then 1 else n * factorial(n-1)
}

method mfactorial1(n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n) {
    f := 1;
    var i:int := n;
    while i > 0
    decreases i
    invariant f * factorial(i) == factorial(n) {
        f, i := i * f, i - 1;
    }
}

method mfactorial2(n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n) {
    f := 1;
    var i:int := 1;
    while i <= n
    decreases n - i
    invariant i <= n + 1
    invariant f == factorial(i-1) {
        f, i := i * f, i + 1;
    }
}

method mfactorial3(n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n) {
    f := 1;
    var i:int := 0;
    while i < n
    decreases n - i
    invariant i <= n
    invariant f == factorial(i) {
        f, i := (i+1) * f, i + 1;
    }
}

lemma {:induction n} factorialSmallerThanExpLemma(n:int)
requires n >= 1
decreases n
ensures factorial(2*n) < exp(2, 2*n) * exp(factorial(n), 2) {
    if n == 1 {
        assert factorial(2) == 2 < 4 * 1 == exp(2, 2) * exp(factorial(1), 2);
    } else {
        calc {
            factorial(2*n);
            == {/* definition of factorial */}
            2*n * factorial(2*n-1);
            == {/* definition of factorial */}
            2*n * (2*n-1) * factorial(2*(n-1));
            < { factorialSmallerThanExpLemma(n-1); }
            2*n * (2*n-1) * exp(2, 2*(n-1)) * exp(factorial(n-1), 2);
            < { assert (2*n-1) < 2*n; }
            2*n * 2*n * exp(2, 2*(n-1)) * exp(factorial(n-1), 2);
            == { assert n * n * exp(factorial(n-1), 2) == factorial(n) * factorial(n) == exp(factorial(n), 2); }
            4 * exp(2, 2*(n-1)) * exp(factorial(n), 2);
            == { assert 4 * exp(2, 2*(n-1)) == exp(2, 2*n); }
            exp(2, 2*n) * exp(factorial(n), 2);
        }
    }
}
