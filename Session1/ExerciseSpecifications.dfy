// specify a method that computes the quotient q and the remain r
// of integer division between a and b
method divide(a:int, b:int) returns (q:int, r:int)
requires a >= 0 && b > 0
ensures a == q * b + r && 0 <= r < b

// specify a method that returns a copy of the argument x
method copy(x:int) returns (y:int)
ensures y == x

// specify a method that returns the maximum of three integers
method max3(x:int, y:int, z:int) returns (m:int)
ensures m >= x && m >= y && m >= z && (m == x || m == y || m == z)

// specify a method that returns a position of the maximum of the array
method posMax1(v:array<int>) returns (i:int)
ensures 0 <= i < v.Length && (forall j :: 0 <= j < v.Length ==> v[j] <= v[i])

// specify a method that returns a position of the maximum of the array
// in segment [c,f)
method posMax(v:array<int>, c:int, f:int) returns (i:int)
requires 0 <= c < f <= v.Length
ensures c <= i < f && (forall j :: c <= j < f ==> v[j] <= v[i])

// specify a method that swaps the values in v in indexes i and j
method swap(v:array<int>, i:int, j:int)
modifies v
requires 0 <= i < v.Length && 0 <= j < v.Length
ensures v[i] == old(v[j]) && v[j] == old(v[i]) && (forall k :: 0 <= k < v.Length && k != i && k != j ==> v[k] == old(v[k]))

// specify a method that modifies the first n positions of v such that all the
// negative values are assigned value 0 and the positive values are unchanged
method positivize(v:array<int>, n:int)
modifies v
requires 0 <= n <= v.Length
ensures forall i :: 0 <= i < v.Length ==> (0 <= i < n ==> ((old(v[i]) < 0 ==> v[i] == 0) && (old(v[i]) > 0 ==> v[i] == old(v[i]))))
    && (n <= i < v.Length ==> v[i] == old(v[i]))
