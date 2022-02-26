// a valid index of the array contains x
predicate appears(v:array<int>, x:int)
reads v {
    exists i :: 0 <= i < v.Length && v[i] == x
}

// a valid index of the array contains 0
predicate existCero(v:array<int>)
reads v {
    appears(v, 0)
}

// all the valid indexes contain strictly positive integers
predicate allPositive(v:array<int>)
reads v {
    forall i :: 0 <= i < v.Length ==> v[i] > 0
}

// x appears exactly once in the array
predicate exactlyOne(v:array<int>, x:int)
reads v {
    exists i :: 0 <= i < v.Length && v[i] == x && (forall j :: 0 <= j < v.Length && j != i ==> v[j] != x)
}

// mathematical function to count the number of times that x appears in v in range [c,f)
function{:fuel 10} count(v:array<int>, x:int, c:int, f:int):(cont:int)
requires 0 <= c <= f <= v.Length
ensures cont >= 0
decreases f - c
reads v {
    if c == f then 0 else
    if v[c] == x then 1 + count(v, x, c+1, f) else count(v, x, c+1, f)
}

// using count define exactlyOnce
predicate exactlyOneWithCount(v:array<int>, x:int)
reads v {
    count(v, x, 0, v.Length) == 1
}

// x is the maximum element of v
predicate isMax(v:array<int>, x:int)
reads v {
    appears(v, x) && forall i :: 0 <= i < v.Length ==> v[i] <= x
}

// i is one position of the minimum of v
predicate posMin(v:array<int>, i:int)
reads v {
    0 <= i < v.Length && forall j :: 0 <= j < v.Length ==> v[i] <= v[j]
}

// each element in v is the double of its index
predicate allDouble(v:array<int>)
reads v {
    forall i :: 0 <= i < v.Length ==> v[i] == 2*i
}

// v is the mirror of w
predicate mirror(v:array<int>, w:array<int>)
reads v, w {
    v.Length == w.Length && forall i :: 0 <= i < v.Length ==> v[i] == w[v.Length - i - 1]
}

// method we want to verify
method main() {
    var a:array<int>;
    a := new[3];
    a[0] := 0; a[1] := 2; a[2] := 4;
    assert allDouble(a);
    assert count(a, 0, 0, 3) == 1;
    assert count(a, 1, 0, 3) == 0;

    var b:array<int>;
    b := new[2];
    b[0] := 1; b[1] := 2;
    //assert !allDouble(b); // this assertion cannot be verified unless we add an extra assertion
    assert b[0] == 1;
    assert !allDouble(b);
    //assert exactlyOne(b, 1); // this assertion takes a very long time to be checked
    assert exactlyOneWithCount(b, 1);
    assert !mirror(a, b);

    var c:array<int>;
    c := new[2];
    c[0] := 1; c[1] := 1;
    assert posMin(c, 0);
    assert posMin(c, 1);
    assert isMax(c, 1);
    assert !exactlyOneWithCount(c, 1);
    assert !exactlyOne(c, 1); // this assertion doesn't require that much time because it can easily find a counterexample
    assert !mirror(b, c);
    assert mirror(c, c);
    assert count(c, 1, 0, 2) == 2;
}
