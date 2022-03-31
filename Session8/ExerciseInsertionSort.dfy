predicate sortedSeg(a:array<int>, i:int, j:int)
reads a
requires 0 <= i <= j + 1 <= a.Length {
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

lemma concatArrays(a:seq<int>, b:seq<int>, i:int, j:int)
requires 0 <= j <= i < |a| == |b|
requires b[..i] + b[i+1..] == a[..j] + a[j+1..]
requires b[i] == a[j]
ensures multiset(b) == multiset(a) {
    assert b[..j] == (b[..i] + b[i+1..])[..j] == a[..j];
    assert b[i+1..] == (b[..i] + b[i+1..])[i..] == a[i+1..];
    assert (b[..i] + b[i+1..])[j..i] == b[j..i];
    assert (a[..j] + a[j+1..])[j..i] == a[j+1..i+1];
    assert b[j..i] == a[j+1..i+1];
    assert b[i] == a[j];
    assert b[j..i+1] == b[j..i] + [b[i]];
    assert multiset(b[j..i+1]) == multiset(b[j..i]) + multiset([b[i]]);
    assert [a[j]] + a[j+1..i+1] == a[j..i+1];
    assert multiset(a[j..i+1]) == multiset([a[j]]) + multiset(a[j+1..i+1]);
    assert b == b[..j] + b[j..i+1] + b[i+1..];
    assert a == a[..j] + a[j..i+1] + a[i+1..];
}

method insertionSort(a:array<int>)
modifies a
ensures sortedSeg(a, 0, a.Length - 1)
ensures multiset(a[..]) == multiset(old(a[..])) {
    var i := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant sortedSeg(a, 0, i-1)
    invariant multiset(a[..]) == multiset(old(a[..])) {
        ghost var b := a[..];
        var temp := a[i];
        var j := i;
        while j > 0 && temp < a[j-1]
        decreases j
        invariant 0 <= j <= i < a.Length
        invariant sortedSeg(a, 0, j-1)
        invariant sortedSeg(a, j+1, i)
        invariant forall k, l :: 0 <= k < j && j < l <= i ==> a[k] <= a[l]
        invariant forall k :: j < k <= i ==> temp < a[k]
        invariant b[..j] == a[..j]
        invariant b[i+1..] == a[i+1..]
        invariant b[j..i] == a[j+1..i+1]
        invariant b[..i] + b[i+1..] == a[..j] + a[j+1..] {
            a[j] := a[j-1];
            j := j - 1;
        }
        assert temp == b[i];
        assert b[..i] + b[i+1..] == a[..j] + a[j+1..];
        a[j] := temp;
        assert b[..i] + b[i+1..] == a[..j] + a[j+1..] && b[i] == a[j];
        concatArrays(a[..], b, i, j);
        i := i + 1;
    }
}
