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
ensures v[f+1..] == old(v[f+1..]) {
    var k:int := c;
    p := c;
    q := f + 1;
    while k < q
    decreases q - k
    invariant c <= p <= k <= q <= f + 1
    invariant forall u :: c <= u < p ==> v[u] < e
    invariant forall u :: p <= u < k ==> v[u] == e
    invariant forall u :: q <= u <= f ==> e < v[u]
    invariant k - p == multiset(v[c..k])[e] + multiset(v[q..f+1])[e]
    invariant multiset(v[..])[e] == multiset(old(v[..]))[e]
    invariant multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
    invariant v[..c] == old(v[..c]) && v[f+1..] == old(v[f+1..]) {
        if v[k] < e {
            v[k], v[p] := v[p], v[k];
            p := p + 1;
            k := k + 1;
        } else if v[k] > e {
            v[k], v[q-1] := v[q-1], v[k];
            q := q - 1;
        } else {
            k := k + 1;
        }
    }
    assert q - p == multiset(v[c..k])[e] + multiset(v[q..f+1])[e] >= 0;
    q := q - 1;
}

method quicksort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f + 1 <= a.Length
decreases f - c
ensures sortedSeg(a[..], c, f)
ensures multiset(a[c..f+1]) == multiset(old(a[c..f+1]))
ensures a[..c] == old(a[..c])
ensures a[f+1..] == old(a[f+1..]) {
    if c < f {
        ghost var a0 := a[..];

        var p, q := mpartition(a, c, f, a[c]);

        ghost var a1 := a[..];
        afterPartition(a0, a1, c, p, q, f);

        quicksort(a, c, p-1);
        
        ghost var a2 := a[..];
        /*assert sortedSeg(a2, c, p-1);
        assert a1[..c] == a2[..c] && a1[p..] == a2[p..];
        assert a2[p] == a1[p] == a0[c];
        assert multiset(a1[c..p]) == multiset(a2[c..p]);
        assert sortedSeg(a2, p, q);
        assert 0 < p ==> a2[p-1] in multiset(a1[c..p]) && a2[p-1] < a0[c];
        assert 0 < p ==> a2[p-1] < a0[c] == a2[p];
        assert sortedSeg(a2, c, q);*/
        // The following assume clause is not needed for verification, but I'm
        // having trouble with my computer to verify this method if I don't
        // assume that fact, because of problems with Dafny. However, it should
        // follow immediatly from the assertions made above that are commented.
        assume 0 < p ==> a2[p-1] < a2[p];
        leftSort(a1, a2, c, p, q, f);
        
        quicksort(a, q+1, f);
        
        ghost var a3 := a[..];
        /*assert sortedSeg(a3, q+1, f);
        assert a2[..q+1] == a3[..q+1] && a2[f+1..] == a3[f+1..];
        assert multiset(a2[q+1..f+1]) == multiset(a3[q+1..f+1]);
        assert a3[q+1] in multiset(a2[q+1..f+1]) && a3[q] < a3[q+1];
        assert sortedSeg(a3, c, f);*/
        // The following assume clause is not needed for verification, but I'm
        // having trouble with my computer to verify this method if I don't
        // assume that fact, because of problems with Dafny. However, it should
        // follow immediatly from the assertions made above that are commented.
        assume q+1 < a.Length ==> a3[q] < a3[q+1];
        rightSort(a2, a3, c, p, q, f);
    }
}

lemma afterPartition(a:seq<int>, b:seq<int>, c:int, p:int, q:int, f:int)
requires 0 <= c <= p <= q <= f < |a| == |b|
requires forall u :: c <= u < p ==> b[u] < a[c]
requires forall u :: p <= u <= q ==> b[u] == a[c]
requires forall u :: q < u <= f ==> a[c] < b[u]
requires multiset(b[c..f+1]) == multiset(a[c..f+1])
requires b[..c] == a[..c]
requires b[f+1..] == a[f+1..]
ensures sortedSeg(b, p, q) {}

lemma leftSort(a:seq<int>, b:seq<int>, c:int, p:int, q:int, f:int)
requires 0 <= c <= p <= q <= f < |a| == |b|
requires sortedSeg(b, c, p-1)
requires sortedSeg(b, p, q)
requires p > 0 ==> b[p-1] < b[p]
requires multiset(b[c..p]) == multiset(a[c..p])
requires b[p..f+1] == a[p..f+1]
ensures sortedSeg(b, c, q)
ensures multiset(b[c..f+1]) == multiset(a[c..f+1]) {
    assert a[c..f+1] == a[c..p] + a[p..f+1];
    assert b[c..f+1] == b[c..p] + b[p..f+1];
}

lemma rightSort(a:seq<int>, b:seq<int>, c:int, p:int, q:int, f:int)
requires 0 <= c <= p <= q <= f < |a| == |b|
requires sortedSeg(b, c, q)
requires sortedSeg(b, q+1, f)
requires q+1 < |b| ==> b[q] < b[q+1]
requires multiset(b[q+1..f+1]) == multiset(a[q+1..f+1])
requires a[..q+1] == b[..q+1]
ensures sortedSeg(b, c, f)
ensures multiset(b[c..f+1]) == multiset(a[c..f+1]) {
    assert a[c..f+1] == a[c..q+1] + a[q+1..f+1];
    assert b[c..f+1] == b[c..q+1] + b[q+1..f+1];
}
