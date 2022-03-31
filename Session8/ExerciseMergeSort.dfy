predicate sortedSeg(a:array<int>, i:int, j:int)
reads a
requires 0 <= i <= j <= a.Length {
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

lemma partitionSequence(s:seq<int>, c:int, m:int, f:int)
requires 0 <= c <= m <= f <= |s|
ensures multiset(s[c..f]) == multiset(s[c..m]) + multiset(s[m..f]) {
    assert s[c..f] == s[c..m] + s[m..f];
}

lemma sorted(mezcla:array<int>, v:array<int>, c:int, f:int)
requires 0 <= c <= f <= v.Length
requires mezcla.Length == f - c
requires mezcla[0..f-c] == v[c..f]
requires sortedSeg(mezcla, 0, f - c)
ensures sortedSeg(v, c, f) {}

method mergeSort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f <= a.Length
decreases f - c
ensures sortedSeg(a, c, f)
ensures multiset(a[c..f]) == multiset(old(a[c..f]))
ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..]) {
    if f > c + 1 {
        var m := (c+f)/2;

        ghost var a0 := a[..];

        mergeSort(a, c, m);

        assert a[m..f] == a0[m..f];
        assert a0[c..f] == a0[c..m] + a0[m..f];
        partitionSequence(a[..], c, m, f);
        assert multiset(a[c..f]) == multiset(a0[c..f]);

        ghost var a1 := a[..];

        mergeSort(a, m, f);

        assert a[c..m] == a1[c..m];
        assert multiset(a[c..m]) == multiset(a1[c..m]) == multiset(a0[c..m]);
        assert multiset(a[m..f]) == multiset(a1[m..f]) == multiset(a0[m..f]);
        partitionSequence(a[..], c, m, f);
        assert multiset(a[c..f]) == multiset(a1[c..f]) == multiset(a0[c..f]);

        ghost var a2 := a[..];
        merge(a, c, m, f);
        assert multiset(a[c..f]) == multiset(a2[c..f]);
    }
}

method {:timeLimitMultiplier 2} merge(v:array<int>, c:int, m:int, f:int)
modifies v
requires 0 <= c <= m <= f <= v.Length
requires sortedSeg(v, c, m)
requires sortedSeg(v, m, f)
ensures sortedSeg(v, c, f)
ensures multiset(v[c..f]) == multiset(old(v[c..f]))
ensures v[..c] == old(v[..c]) && v[f..] == old(v[f..]) {
    var i := c;
    var j := m;
    var k := 0;
    var mezcla := new int[f-c];

    while i < m && j < f
    decreases f + m - i - j
    invariant c <= i <= m <= j <= f <= v.Length
    invariant k == i - c + j - m
    invariant 0 <= k <= f - c
    invariant sortedSeg(mezcla, 0, k)
    invariant sortedSeg(v, c, m)
    invariant sortedSeg(v, m, f)
    invariant k > 0 ==> forall u :: i <= u < m ==> mezcla[k-1] <= v[u]
    invariant k > 0 ==> forall u :: j <= u < f ==> mezcla[k-1] <= v[u]
    invariant multiset(mezcla[..k]) == multiset(v[c..i] + v[m..j])
    invariant multiset(v[c..f]) == multiset(old(v[c..f]))
    invariant v[..c] == old(v[..c]) && v[f..] == old(v[f..]) {
        assert sortedSeg(mezcla, 0, k);
        assert sortedSeg(v, c, m);
        assert sortedSeg(v, m, f);
        if v[i] <= v[j] {
            mezcla[k] := v[i];
            i := i + 1;
        } else {
            mezcla[k] := v[j];
            j := j + 1;
        }
        k := k + 1;
    }

    while i < m
    decreases m - i
    invariant c <= i <= m <= j <= f
    invariant k == i - c + j - m
    invariant 0 <= k <= f - c
    invariant sortedSeg(mezcla, 0, k)
    invariant sortedSeg(v, c, m)
    invariant sortedSeg(v, m, f)
    invariant k > 0 ==> forall u :: i <= u < m ==> mezcla[k-1] <= v[u]
    invariant k > 0 ==> forall u :: j <= u < f ==> mezcla[k-1] <= v[u]
    invariant multiset(mezcla[..k]) == multiset(v[c..i] + v[m..j])
    invariant multiset(v[c..f]) == multiset(old(v[c..f]))
    invariant v[..c] == old(v[..c]) && v[f..] == old(v[f..]) {
        mezcla[k] := v[i];
        i := i + 1;
        k := k + 1;
    }

    while j < f
    decreases f - j
    invariant c <= i <= m <= j <= f
    invariant k == i - c + j - m
    invariant 0 <= k <= f - c
    invariant sortedSeg(mezcla, 0, k)
    invariant sortedSeg(v, c, m)
    invariant sortedSeg(v, m, f)
    invariant k > 0 ==> forall u :: i <= u < m ==> mezcla[k-1] <= v[u]
    invariant k > 0 ==> forall u :: j <= u < f ==> mezcla[k-1] <= v[u]
    invariant multiset(mezcla[..k]) == multiset(v[c..i] + v[m..j])
    invariant multiset(v[c..f]) == multiset(old(v[c..f]))
    invariant v[..c] == old(v[..c]) && v[f..] == old(v[f..]) {
        mezcla[k] := v[j];
        j := j + 1;
        k := k + 1;
    }

    assert i == m && j == f;
    assert multiset(mezcla[..f-c]) == multiset(v[c..m] + v[m..f]);
    assert v[c..m] + v[m..f] == v[c..f];
    assert multiset(old(v[c..f])) == multiset(mezcla[..f-c]);
    assert sortedSeg(mezcla, 0, f - c);

    var l := 0;
    while l < f - c
    decreases f - c - l
    invariant 0 <= l <= f - c
    invariant mezcla[..l] == v[c..c+l]
    invariant sortedSeg(mezcla, 0, f - c)
    invariant sortedSeg(v, c, c + l)
    invariant multiset(old(v[c..f])) == multiset(mezcla[..f-c])
    invariant v[..c] == old(v[..c]) && v[f..] == old(v[f..]) {
        v[c+l] := mezcla[l];
        l := l + 1;
    }

    assert sortedSeg(mezcla, 0, f - c);
    sorted(mezcla, v, c, f);
    assert sortedSeg(v, c, f);
}
