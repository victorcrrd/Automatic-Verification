predicate sortedSeg(a:seq<int>, i:int, j:int)
requires 0 <= i <= j + 1 <= |a| {
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

method mpartition(v:array<int>, c:int, f:int, e:int) returns (p:int, q:int)
modifies v
requires 0 <= c <= f < v.Length
requires e in v[c..f+1]
ensures c <= p <= q <= f
ensures forall u :: c <= u < p ==> v[u] < e
ensures forall u :: p <= u <= q ==> v[u] == e
ensures forall u :: q < u <= f ==> e < v[u]
ensures multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
ensures v[..c] == old(v[..c])
ensures v[f+1..] == old(v[f+1..])

method /*{:timeLimitMultiplier 2}*/ quicksort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f + 1 <= a.Length
decreases f - c
ensures sortedSeg(a[..], c, f)
ensures multiset(a[c..f+1]) == multiset(old(a[c..f+1]))
ensures a[..c] == old(a[..c])
ensures a[f+1..] == old(a[f+1..]) {
    if c < f {
        var p, q := mpartition(a, c, f, a[c]);
        ghost var a1 := a[..];
        quicksort(a, c, p-1);
        ghost var a2 := a[..];
        quicksort(a, q+1, f);
    }
}
