function min(v:array<int>, i:int):int
requires 1 <= i <= v.Length
decreases i
reads v
ensures forall k :: 0 <= k < i ==> min(v, i) <= v[k] {
    if i == 1 then v[0]
    else if v[i-1] <= min(v, i-1) then v[i-1]
    else min(v, i-1)
}

function countMin(v:array<int>, x:int, i:int):int
requires 0 <= i <= v.Length
decreases i
reads v
ensures !(x in v[0..i]) ==> countMin(v, x, i) == 0 {
    if i == 0 then 0
    else countMin(v, x, i-1) + (if v[i-1] == x then 1 else 0)
}

method mcountMin(v:array<int>) returns (c:int)
requires v.Length > 0
ensures c == countMin(v, min(v, v.Length), v.Length) {
    var i:int := 1;
    c := 1;
    var m:int := v[0];
    while i < v.Length
    decreases v.Length - i
    invariant 1 <= i <= v.Length
    invariant m == min(v, i)
    invariant c == countMin(v, min(v, i), i) {
        if v[i] < m {
            m := v[i];
            c := 1;
        } else if v[i] == m {
            c := c + 1;
        }
        i := i + 1;
    }
}


/*


 method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm
*/