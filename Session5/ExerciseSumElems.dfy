function sumR(s:seq<int>):int
decreases s {
    if s == [] then 0
    else sumR(s[..|s|-1]) + s[|s|-1]
}

function sumL(s:seq<int>):int
decreases s {
    if s == [] then 0
    else s[0] + sumL(s[1..])
}

lemma concatLast(s:seq<int>, t:seq<int>)
requires t != []
ensures (s+t)[..|s+t|-1] == s+(t[..|t|-1]) {}

lemma concatFirst(s:seq<int>, t:seq<int>)
requires s != []
ensures (s+t)[1..] == s[1..]+t {}

lemma {:induction s, t} sumByPartsR(s:seq<int>, t:seq<int>)
decreases s, t
ensures sumR(s+t) == sumR(s) + sumR(t) {
    if t == [] {
        assert s+t == s;
    } else if s == [] {
        assert s+t == t;
    } else {
        calc == {
            sumR(s+t);
            sumR((s+t)[..|s+t|-1]) + (s+t)[|s+t|-1];
            sumR((s+t)[..|s+t|-1]) + t[|t|-1];
            { concatLast(s, t); }
            sumR(s+t[..|t|-1]) + t[|t|-1];
            { sumByPartsR(s, t[..|t|-1]); }
            sumR(s) + sumR(t[..|t|-1]) + t[|t|-1];
            sumR(s) + sumR(t);
        }
    }
}

lemma {:induction s, t} sumByPartsL(s:seq<int>, t:seq<int>)
decreases s, t
ensures sumL(s+t) == sumL(s) + sumL(t) {
    if t == [] {
        assert s+t == s;
    } else if s == [] {
        assert s+t == t;
    } else {
        calc == {
            sumL(s+t);
            (s+t)[0] + sumL((s+t)[1..]);
            s[0] + sumL((s+t)[1..]);
            { concatFirst(s, t); }
            s[0] + sumL(s[1..]+t);
            { sumByPartsL(s[1..], t); }
            s[0] + sumL(s[1..]) + sumL(t);
            sumL(s) + sumL(t);
        }
    }
}

lemma {:induction s, i, j} equalSum(s:seq<int>, i:int, j:int)
requires 0 <= i <= j <= |s|
decreases j - i
ensures sumR(s[i..j]) == sumL(s[i..j]) {
    if i == j {
        assert sumR(s[i..j]) == sumR([]) == sumL([]) == sumL(s[i..j]);
    } else if i + 1 == j {
        assert sumR(s[i..j]) == s[i] == sumL(s[i..j]);
    } else {
        ghost var sij := s[i..j];
        calc == {
            sumR(sij);
            sumR(sij[..j-i-1]) + sij[j-i-1];
            { equalSum(sij, 0, j-i-1); }
            sumL(sij[..j-i-1]) + sij[j-i-1];
            sij[0] + sumL(sij[1..j-i-1]) + sij[j-1-i];
            { equalSum(sij, 1, j-i-1); }
            sij[0] + sumR(sij[1..j-i-1]) + sij[j-1-i];
            { assert sij[1..j-i-1] == (sij[1..])[..j-i-2]; }
            sij[0] + sumR(sij[1..]);
            { equalSum(sij, 1, j-i); }
            sij[0] + sumL(sij[1..]);
            sumL(sij);
        }
    }
}

lemma equalSumV()
ensures forall v:array<int>, i, j | 0 <= i <= j <= v.Length :: sumR(v[i..j]) == sumL(v[i..j]) {
    forall v:array<int>, i, j | 0 <= i <= j <= v.Length
    ensures sumR(v[i..j]) == sumL(v[i..j]) {
        equalSum(v[..], i, j);
    }
}

function sumV(v:array<int>, c:int, f:int):int
requires 0 <= c <= f <= v.Length
reads v {
    sumR(v[c..f])
}

lemma arrayFacts<T>()
ensures forall v:array<T> :: v[..v.Length] == v[..]
ensures forall v:array<T> :: v[0..] == v[..]
ensures forall v:array<T> :: v[0..v.Length] == v[..]
ensures forall v:array<T> :: |v[0..v.Length]| == v.Length
ensures forall v:array<T> | v.Length >= 1 :: |v[1..v.Length]| == v.Length-1
ensures forall v:array<T> :: forall k:nat | k < v.Length :: v[..k+1][..k] == v[..k] {}

method sumElems(v:array<int>) returns (sum:int)
ensures sum == sumV(v, 0, v.Length) {
    arrayFacts<int>();
    sum := 0;
    var i:int := 0;
    while i < v.Length
    decreases v.Length - i
    invariant i <= v.Length
    invariant sum == sumV(v, 0, i) {
        sum := sum + v[i];
        i := i + 1;
    }
}

method sumElemsB(v:array<int>) returns (sum:int)
ensures sum == sumR(v[0..v.Length]) {
    equalSumV();
    arrayFacts<int>();
    sum := 0;
    var i:int := v.Length;
    while i > 0
    decreases i
    invariant i >= 0
    invariant sum == sumV(v, i, v.Length) {
        sum := sum + v[i-1];
        i := i - 1;
    }
}
