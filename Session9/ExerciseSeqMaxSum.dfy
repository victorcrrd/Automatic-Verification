function sum(v:array<int>, i:int, j:int) : int
reads v
requires 0 <= i <= j <= v.Length
decreases j {
    if i == j then 0
    else sum(v, i, j-1) + v[j-1]
}

predicate sumMaxToRight(v:array<int>, i:int, s:int)
reads v
requires 0 <= i < v.Length {
    forall l, j {:induction l} :: 0 <= l <= i && j == i + 1 ==> sum(v, l, j) <= s
}

method segMaxSum(v:array<int>, i:int) returns (s:int, k:int)
requires 0 <= i < v.Length
ensures 0 <= k <= i
ensures s == sum(v, k, i+1)
ensures sumMaxToRight(v, i, s) {
    s := v[0];
    k := 0;
    var j := 0;
    while j < i
    decreases i - j
    invariant 0 <= k <= j <= i
    invariant s == sum(v, k, j + 1)
    invariant sumMaxToRight(v, j, s) {
        if s + v[j+1] > v[j+1] {
            s := s + v[j+1];
        } else {
            s := v[j+1];
            k := j + 1;
        }
        j := j + 1;
    }
}

function sum2(v:array<int>, i:int, j:int) : int
reads v
requires 0 <= i <= j <= v.Length
decreases j - i {
    if i == j then 0
    else v[i] + sum2(v, i + 1, j)
}

predicate sumMaxToRight2(v:array<int>, i:int, j:int, s:int)
reads v
requires 0 <= i <= j < v.Length {
    forall l, k {:induction l} :: i <= l <= j && k == j + 1 ==> sum2(v, l, k) <= s
}

method segMaxSum2(v:array<int>, i:int) returns (s:int, k:int)
requires 0 <= i < v.Length
ensures 0 <= k <= i
ensures s == sum2(v, k, i + 1)
ensures sumMaxToRight2(v, 0, i, s) {
    var current:int := v[i];
    s := v[i];
    k := i;
    var j := i;
    while j > 0
    decreases j
    invariant 0 <= j <= k <= i
    invariant current == sum2(v, j, i + 1)
    invariant s == sum2(v, k, i + 1)
    invariant sumMaxToRight2(v, j, i, s) {
        current := current + v[j-1];
        if current > s {
            s := current;
            k := j - 1;
        }
        j := j - 1;
    }
}
