// x is strictly positive
predicate positive(x:int) {
    x > 0
}

// y is the double of x
predicate isDouble(x:int, y:int) {
    y == 2*x
}

// x is even
predicate even(x:int) {
    x % 2 == 0
}

// define the mathematical function n!
function factorial(n:int):(f:int) 
requires n >= 0 {
    if n == 0 then 1 else n * factorial(n-1)
}

// x is equal to n!
predicate isFactorial(x:int, n:int)
requires n >= 0 {
    x == factorial(n)
}

// x is in the interval [c,f)
predicate between(x:int, c:int, f:int) {
    c <= x < f
}

// either x is the triple of y or viceversa
predicate triple(x:int, y:int) {
    x == 3*y || y == 3*x
}

// all valid indexes contain positive integers
predicate allPositive(v:array<int>)
reads v {
    forall i :: 0 <= i < v.Length ==> v[i] >= 0
}

// there exist an index containing a positive integer
predicate existPositive(v:array<int>)
reads v {
    exists i :: 0 <= i < v.Length && v[i] >= 0
}

// method we want to verify
method main() {
    var x:int; var y:int; var z:int;
    x := 1;
    assert positive(x);

    x := -2;
    assert !positive(x);

    x := 2; y := 4; z := 3;
    assert isDouble(x, y);
    assert !isDouble(x, z);

    z := -3;
    assert even(y);
    assert !even(z);

    z := 6;
    assert isFactorial(x, x);
    assert isFactorial(z, 3);

    // conjunction and disjunction
    assert between(y, x, z) && between(x, 0, 10);
    assert !between(x, x, x);

    assert triple(z, x);
    assert triple(x, z);
    assert !triple(x, y);

    // negation
    assert !even(9);
    assert !between(x, x, x) && !triple(x, y);

    // implication
    assert even(x) ==> even(2*x);
    assert positive(x) ==> positive(x+2);
    assert isDouble(x, y) ==> isDouble(3*x, 3*y);

    // false premise
    z := 3;
    assert even(z) ==> even(z+1);

    // universal quantification
    var a:array<int>;
    a := new[3];
    a[0] := 1; a[1] := 7; a[2] := 3;
    assert allPositive(a);
    a[1] := -9;
    assert !allPositive(a);

    // existential quantification: we need to assert that a[0] >= 0 for the exists to work
    a[1] := -9;
    assert a[0] >= 0; //needed: existential problems
    assert existPositive(a);
}
