method mmaximumLeftToRight(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length
ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k] {
    var j:int := 1;
    i := 0;
    while j < v.Length
    decreases v.Length - j
    invariant 0 <= i < j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k] {
        if v[j] > v[i] {
            i := j;
        }
        j := j + 1;
    }
}

method mmaximumRightToLeft(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length
ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k] {
    var j:int := v.Length - 2;
    i := v.Length - 1;
    while 0 <= j
    decreases j
    invariant -1 <= j < i < v.Length
    invariant forall k :: j < k < v.Length ==> v[i] >= v[k] {
        if v[j] > v[i] {
            i := j;
        }
        j := j - 1;
    }
}

method mmaximumFirstLeftToRight(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length
ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
ensures forall k :: 0 <= k < i ==> v[i] > v[k] {
    var j:int := 1;
    i := 0;
    while j < v.Length
    decreases v.Length - j
    invariant 0 <= i < j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall k :: 0 <= k < i ==> v[i] > v[k] {
        if v[j] > v[i] {
            i := j;
        }
        j := j + 1;
    }
}

method mmaximumFirstRightToLeft(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length
ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
ensures forall k :: 0 <= k < i ==> v[i] > v[k] {
    var j:int := v.Length - 2;
    i := v.Length - 1;
    while j >= 0
    decreases j
    invariant -1 <= j < i < v.Length
    invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
    invariant forall k :: j < k < i ==> v[i] > v[k] {
        if v[j] >= v[i] {
            i := j;
        }
        j := j - 1;
    }
} 


method mmaximumLastLeftToRight(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length
ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
ensures forall k :: i < k < v.Length ==> v[i] > v[k] {
    var j:int := 1;
    i := 0;
    while j < v.Length
    decreases v.Length - j
    invariant 0 <= i < j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall k :: i < k < j ==> v[i] > v[k] {
        if v[j] >= v[i] {
            i := j;
        }
        j := j + 1;
    }
}

method mmaximumLastRightToLeft(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length
ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
ensures forall k :: i < k < v.Length ==> v[i] > v[k] {
    var j:int := v.Length - 2;
    i := v.Length - 1;
    while j >= 0
    decreases j
    invariant -1 <= j < i < v.Length
    invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
    invariant forall k :: i < k < v.Length ==> v[i] > v[k] {
        if v[j] > v[i] {
            i := j;
        }
        j := j - 1;
    }
}

method mmaxvalue(v:array<int>) returns (m:int)
requires v.Length > 0
ensures m in v[0..v.Length]
ensures forall i :: 0 <= i < v.Length ==> v[i] <= m {
    var i:int := 1;
    m := v[0];
    while i < v.Length
    decreases v.Length - i
    invariant i <= v.Length
    invariant m in v[0..i]
    invariant forall j :: 0 <= j < i ==> m >= v[j] {
        if v[i] > m {
            m := v[i];
        }
        i := i + 1;
    }
}
