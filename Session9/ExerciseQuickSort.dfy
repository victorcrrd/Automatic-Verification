predicate sortedSeg(a:seq<int>, i:int, j:int)
requires 0 <= i <= j + 1 <= |a| {
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

lemma multisetPreservesSmaller(a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires 0 <= c <= f + 1 <= |a| == |b|
requires forall j :: c <= j <= f ==> a[j] <= x
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures forall j :: c <= j <= f ==> b[j] <= x {
    assert forall z :: z in multiset(a[c..f+1]) ==> z <= x;
}

lemma multisetPreservesGreater(a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires 0 <= c <= f + 1 <= |a| == |b|
requires forall j :: c <= j <= f ==> a[j] >= x
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures forall j :: c <= j <= f ==> b[j] >= x {
    assert forall z :: z in multiset(a[c..f+1]) ==> z >= x;
}

lemma seqSplit(s:seq<int>, c:int, p:int, f:int)
requires 0 <= c <= p <= f + 1 <= |s|
ensures multiset(s[c..f+1]) == multiset(s[c..p]) + multiset(s[p..f+1]) {
    assert s[c..f+1] == s[c..p] + s[p..f+1];
}

method partition(v:array<int>, c:int, f:int) returns (p:int)
modifies v
requires 0 <= c <= f < v.Length
ensures c <= p <= f
ensures forall u :: c <= u <= p ==> v[u] <= v[p]
ensures forall u :: p < u <= f ==> v[p] <= v[u]
ensures multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
ensures v[..c] == old(v[..c]) && v[f+1..] == old(v[f+1..]) {
    var i, j := c+1, f;
    while i <= j
    decreases j - i
    invariant c + 1  <= i <= j + 1 <= f + 1
    invariant forall u :: c + 1 <= u < i ==> v[u] <= v[c]
    invariant forall u :: j + 1 <= u <= f ==> v[c] <= v[u]
    invariant multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
    invariant v[..c] == old(v[..c]) && v[f+1..] == old(v[f+1..]) {
        if v[i] <= v[c] {
            i := i + 1;
        } else if v[c] <= v[j] {
            j := j - 1;
        } else {
            v[i], v[j] := v[j], v[i];
            i := i + 1;
            j := j - 1;
        }
    }
    p := j;
    v[c], v[p] := v[p], v[c];
}

method quickSort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f + 1 <= a.Length
decreases f - c
ensures sortedSeg(a[..], c, f)
ensures multiset(a[c..f+1]) == multiset(old(a[c..f+1]))
ensures a[..c] == old(a[..c]) && a[f+1..] == old(a[f+1..]) {
    if c < f {
        ghost var a0 := a[..];

        var p := partition(a, c, f);

        ghost var a1 := a[..];
        assert forall u :: c <= u <= p ==> a1[u] <= a1[p];
        assert forall u :: p < u <= f ==> a1[p] <= a1[u];

        quickSort(a, c, p-1);

        ghost var a2 := a[..];
        assert multiset(a2[c..p]) == multiset(a1[c..p]);
        assert a2[p..f+1] == a1[p..f+1];
        seqSplit(a1, c, p, f);
        seqSplit(a2, c, p, f);
        assert multiset(a2[c..f+1]) == multiset(a1[c..f+1]);
        multisetPreservesSmaller(a1, a2, c, p-1, a[p]);

        quickSort(a, p+1, f);
        ghost var a3 := a[..];
        assert multiset(a3[p+1..f+1]) == multiset(a2[p+1..f+1]);
        assert a3[c..p+1] == a2[c..p+1];
        seqSplit(a2, c, p+1, f);
        seqSplit(a3, c, p+1, f);
        assert multiset(a3[c..f+1]) == multiset(a2[c..f+1]);
        multisetPreservesGreater(a2, a3, p+1, f, a[p]);
    }
}
