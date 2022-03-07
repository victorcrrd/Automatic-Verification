predicate positive(s:seq<int>) {
    forall i :: 0 <= i < |s| ==> s[i] >= 0
}

predicate isEven(i:int)
requires i >= 0 {
    i % 2 == 0
}

function countEven(s:seq<int>):int
requires positive(s)
decreases s {
    if s == [] then 0
    else countEven(s[..|s|-1]) + (if isEven(s[|s|-1]) then 1 else 0)
}

lemma ArrayFacts<T>()
    ensures forall v:array<T> :: v[..v.Length] == v[..]
    ensures forall v:array<T> :: v[0..] == v[..]
    ensures forall v:array<T> :: v[0..v.Length] == v[..]
    ensures forall v:array<T> :: |v[0..v.Length]| == v.Length
    ensures forall v:array<T> | v.Length > 0 :: |v[1..v.Length]| == v.Length - 1
    ensures forall v:array<T> :: forall k:nat | k < v.Length :: v[..k+1][..k] == v[..k] {}

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures n == countEven(v[..]) {
    ArrayFacts<int>();
    n := 0;
    var i:int := 0;
    while i < v.Length
    decreases v.Length - i
    invariant i <= v.Length
    invariant n == countEven(v[..i]) {
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        i := i + 1;
    }
}
