predicate strictNegative(v:array<int>, i:int, j:int)
reads v
requires 0 <= i <= j <= v.Length {
    forall u | i <= u < j :: v[u] < 0
}

predicate positive(s:seq<int>) {
    forall u :: 0 <= u < |s| ==> s[u] >=0
}

predicate isPermutation(s:seq<int>, t:seq<int>) {
    multiset(s) == multiset(t)
}

method separate(v:array<int>) returns (i:int)
modifies v
ensures 0 <= i <= v.Length
ensures positive(v[..i])
ensures strictNegative(v, i, v.Length)
ensures isPermutation(v[..], old(v[..])) {
    if v.Length == 0 {
        i := 0;
        return;
    }
    assert v.Length > 0;
    var p, q:int := 0, v.Length - 1;
    while p <= q
    decreases q - p
    invariant 0 <= p <= q + 1 <= v.Length
    invariant positive(v[..p])
    invariant strictNegative(v, q+1, v.Length)
    invariant isPermutation(v[..], old(v[..])) {
        if v[p] >= 0 {
            p := p + 1;
        } else {
            v[p], v[q] := v[q], v[p];
            q := q - 1;
        }
    }
    i := p;
}
