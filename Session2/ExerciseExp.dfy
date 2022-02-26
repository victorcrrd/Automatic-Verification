// exponential function
function exp(b:int, e:int):int
requires e >= 0
decreases e {
    if e == 0 then 1 else b * exp(b, e-1)
}

// exponential function is at least 1 for positive bases
lemma expAtLeast1(b:int, e:int)
requires b >= 1 && e >= 0
ensures exp(b, e) >= 1 {}

// exponential is increasing in the first argument
lemma expIncreasing(b:int, e:int)
requires b >= 1 && e >= 0
decreases e
ensures exp(b, e) <= exp(b+1, e) {
    if e == 0 {
        assert exp(b, 0) <= exp(b+1, 0);
    } else {
        expIncreasing(b, e-1);
        assert b >= 1;
        expAtLeast1(b, e-1);
        assert b * exp(b, e-1) <= (b+1) * exp(b+1, e-1);
    }
}

// powers of 3 are odd numbers
lemma exp3Lemma(n:int)
requires n >= 1
decreases n
ensures (exp(3, n)-1) % 2 == 0 {
    if n == 1 {
        assert exp(3, 1)-1 == 2;
    } else {
        exp3Lemma(n-1);
        assert (exp(3, n-1)-1) % 2 == 0;
        assert exp(3, n)-1 == 2 * exp(3, n-1) + exp(3, n-1)-1;
    }
}

// pair powers of 3 are congruent with 1 mod 8
lemma mult8Lemma(n:int)
requires n >= 1
decreases n
ensures (exp(3, 2*n)-1) % 8 == 0 {
    if n == 1 {
        assert exp(3, 2)-1 == 8;
    } else {
        mult8Lemma(n-1);
        assert (exp(3, 2*(n-1))-1) % 8 == 0;
        assert exp(3, 2*n)-1 == 9*(exp(3, 2*(n-1))-1) + 8;
    }
}
