predicate positive(s:seq<int>) {
    forall i :: 0 <= i < |s| ==> s[i] >= 0
}

method mpositive1(v:array<int>) returns (b:bool)
ensures b == positive(v[0..v.Length]) {
    var i:int := 0;
    b := true;
    while i < v.Length
    decreases v.Length - i 
    invariant i <= v.Length && b == positive(v[0..i]) {
        if v[i] < 0 {
            b := false;
        }
        i := i + 1;
    }
}

method mpositive2(v:array<int>) returns (b:bool)
ensures b == positive(v[0..v.Length]) {
    var i:int := 0;
    while i < v.Length && v[i] >= 0
    decreases v.Length - i
    invariant i <= v.Length && positive(v[0..i]) {
        i := i + 1;
    }
    b := i == v.Length;
}

method mpositive3(v:array<int>) returns (b:bool)
ensures b == positive(v[0..v.Length]) {
    var i:int := 0;
    b := true;
    while i < v.Length && b
    decreases v.Length - i
    invariant i <= v.Length && b == positive(v[0..i]) && (!b ==> forall j :: i <= j <= v.Length ==> !positive(v[0..j])) {
        if v[i] < 0 {
            b := false;
        }
        i := i + 1;
    }
}

method mpositive4(v:array<int>) returns (b:bool)
ensures b == positive(v[0..v.Length]) {
    var i:int := 0;
    b := true;
    while i < v.Length && b
    decreases v.Length - i
    invariant i <= v.Length && b == positive(v[0..i]) && (!b ==> !positive(v[0..v.Length])) {
        b := v[i] >= 0;
        i := i + 1;
    }
}

method mpositive5(v:array<int>) returns (b:bool)
ensures b == positive(v[0..v.Length]) {
    var i:int := 0;
    b := true;
    while i < v.Length && b
    decreases if b then v.Length - i else v.Length - i - 1
    invariant i <= v.Length && (b ==> positive(v[0..i])) && (!b ==> 0 <= i < v.Length && v[i] < 0) {
        if v[i] < 0 {
            b := false;
        } else {
            i := i + 1;
        }
    }
}
