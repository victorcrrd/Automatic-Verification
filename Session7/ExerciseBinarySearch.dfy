predicate sorted(s:seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
requires sorted(v[..])
ensures -1 <= p < v.Length
ensures forall u :: 0 <= u <= p ==> v[u] <= elem
ensures forall u :: p < u < v.Length ==> elem < v[u] {
    var c, f:int := 0, v.Length - 1;
    while c <= f
    decreases f - c
    invariant 0 <= c <= v.Length
    invariant -1 <= f < v.Length
    invariant c <= f + 1
    invariant forall u :: 0 <= u < c ==> v[u] <= elem
    invariant forall u :: f < u < v.Length ==> elem < v[u] {
        var m:int := (c+f)/2;
        if v[m] <= elem {
            c := m + 1;
        } else {
            f := m - 1;
        }
    }
    p := c - 1;
}

method search(v:array<int>, elem:int) returns (b:bool)
requires sorted(v[..])
ensures b == (elem in v[..]) {
    var p:int := binarySearch(v, elem);
    b := p != -1 && v[p] == elem;
}

method {:tailrecursion false} binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
requires sorted(v[..])
requires 0 <= c <= f + 1 <= v.Length
requires forall k :: 0 <= k < c ==> v[k] <= elem
requires forall k :: f < k < v.Length ==> elem < v[k]
decreases f - c
ensures -1 <= p < v.Length
ensures forall u :: 0 <= u <= p ==> v[u] <= elem
ensures forall u :: p < u < v.Length ==> elem < v[u] {
    if c == f + 1 {
        p := c - 1;
    } else {
        var m:int := (c+f)/2;
        if v[m] <= elem {
            p := binarySearchRec(v, elem, m+1, f);
        } else {
            p := binarySearchRec(v, elem, c, m-1);
        }
    }
}

method otherBinarySeach(v:array<int>, elem:int) returns (b:bool, p:int)
requires sorted(v[..])
ensures 0 <= p <= v.Length
ensures b == (elem in v[..])
ensures b ==> p < v.Length && v[p] == elem
ensures !b ==> forall u :: 0 <= u < p ==> v[u] <= elem
ensures !b ==> forall u :: p <= u < v.Length ==> elem < v[u] {
    var c, f:int := 0, v.Length;
    var m:int;
    while c < f
    decreases f - c
    invariant 0 <= c <= f <= v.Length
    invariant forall u :: 0 <= u < c ==> v[u] < elem
    invariant forall u :: f <= u < v.Length ==> elem < v[u] {
        m := (c+f)/2;
        if v[m] > elem {
            f := m;
        } else if v[m] < elem {
            c := m + 1;
        } else { // v[m] == elem
            b := true;
            p := m;
            return;
        }
    }
    p := f;
    b := p < v.Length && v[p] == elem;
}
