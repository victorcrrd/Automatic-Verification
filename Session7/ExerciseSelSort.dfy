predicate sortedSeg(a:array<int>, i:int, j:int)
reads a
requires 0 <= i <= j <= a.Length {
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

method selSort(a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f <= a.Length
ensures sortedSeg(a, c, f)
ensures multiset(a[c..f]) == multiset(old(a[c..f]))
ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..]) {
    if c <= f - 1 {
        var i:int := c;
        while i < f - 1
        decreases f - i
        invariant 0 <= c <= i <= f <= a.Length
        invariant sortedSeg(a, c, i)
        invariant forall l, k :: c <= l < i <= k < f ==> a[l] <= a[k]
        invariant multiset(a[c..f]) == multiset(old(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..]) {
            ghost var b := a[..];
            var less:int := i;
            var j:int := i + 1;
            while j < f
            decreases f - j
            invariant 0 <= c <= i < j <= f <= a.Length
            invariant i <= less < f
            invariant multiset(a[c..f]) == multiset(old(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant forall k :: i <= k < j ==> a[less] <= a[k] {
                if a[j] < a[less] {
                    less := j;
                }
                j := j + 1;
            }
            a[i], a[less] := a[less], a[i];
            i := i + 1;
        }
    }
}
