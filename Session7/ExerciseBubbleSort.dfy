predicate sortedSeg(a:array<int>, i:int, j:int)
reads a
requires 0 <= i <= j <= a.Length {
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

method bubbleSort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f <= a.Length
ensures sortedSeg(a, c, f)
ensures multiset(a[c..f]) == multiset(old(a[c..f]))
ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..]) {
    var i:int := c;
    while i < f
    decreases f - i
    invariant c <= i <= f
    invariant sortedSeg(a, c, i)
    invariant forall l, k :: c <= l < i && i <= k < f ==> a[l] <= a[k]
    invariant multiset(a[c..f]) == multiset(old(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..]) {
        ghost var b := a[..];
        var j := f - 1;
        while i < j
        decreases j - i
        invariant i <= j < f
        invariant forall k :: j < k < f ==> a[j] <= a[k]
        invariant multiset(a[c..f]) == multiset(old(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant forall l :: c <= l < i < a.Length ==> b[l] == a[l]
        invariant forall l, k :: c <= l < i && i <= k < f ==> a[l] <= a[k] {
            if a[j-1] > a[j] {
                a[j-1], a[j] := a[j], a[j-1];
            }
            j := j - 1;
        }
        i := i + 1;
    }
}

method otherBubbleSort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f <= a.Length
ensures sortedSeg(a, c, f)
ensures multiset(a[c..f]) == multiset(old(a[c..f]))
ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..]) {
    var i := c;
    var b := true;
    while i < f && b
    decreases f - i
    invariant c <= i <= f <= a.Length
    invariant sortedSeg(a, c, i)
    invariant forall l, k :: c <= l < i && i <= k < f ==> a[l] <= a[k]
    invariant multiset(a[c..f]) == multiset(old(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant !b ==> sortedSeg(a, i, f) {
        ghost var d := a[..];
        var j := f - 1;
        b := false;
        while i < j
        decreases j - i
        invariant c <= i <= j < f <= a.Length
        invariant multiset(d[c..f]) == multiset(a[c..f]) == multiset(old(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant forall k :: j < k < f ==> a[j] <= a[k]
        invariant forall l :: c <= l < i < a.Length ==> d[l] == a[l]
        invariant forall l, k :: c <= l < i && i <= k < f ==> a[l] <= a[k]
        invariant !b ==> sortedSeg(a, j, f) {
            if a[j-1] > a[j] {
                a[j-1], a[j] := a[j], a[j-1];
                assert multiset(d[c..f]) == multiset(a[c..f]) == multiset(old(a[c..f])); //somehow necessary
                b := true;
            }
            j := j - 1;
        }
        i := i + 1;
    }
}
