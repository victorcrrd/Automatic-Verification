predicate isPeak(v:array<int>, i:int)
requires 0 <= i < v.Length
reads v {
    forall k :: 0 <= k < i ==> v[k] <= v[i]
}

function peakSum(v:array<int>, i:int):int
requires 0 <= i <= v.Length
reads v
decreases i {
    if i == 0 then 0
    else peakSum(v, i-1) + (if isPeak(v, i-1) then v[i-1] else 0)
}

method mpeakSum(v:array<int>) returns (sum:int)
requires v.Length > 0
ensures sum == peakSum(v, v.Length) {
    var i:int := 1;
    sum := v[0];
    var max:int := v[0];
    while i < v.Length
    decreases v.Length - i
    invariant i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] <= max
    invariant exists k :: 0 <= k < i && v[k] == max
    invariant sum == peakSum(v, i) {
        if max <= v[i] {
            max := v[i];
            sum := sum + v[i];
        }
        i := i + 1;
    }
}
