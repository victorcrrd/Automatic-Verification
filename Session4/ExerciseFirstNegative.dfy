predicate positive(s:seq<int>) {
    forall i :: 0 <= i < |s| ==> s[i] >= 0
}

method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists j :: 0 <= j < v.Length && v[j] < 0
ensures b ==> 0 <= i < v.Length && v[i] < 0 && positive(v[0..i]) {
    i := 0;
    b := false;
    while i < v.Length && !b
    decreases v.Length - i
    invariant i <= v.Length
    invariant !b ==> positive(v[..i])
    invariant b ==> i > 0 && v[i-1] < 0 && positive(v[..i-1]) {
        b := v[i] < 0;
        i := i + 1;
    }
    if b {
        i := i - 1;
    }
}

method mfirstNegative2(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists j :: 0 <= j < v.Length && v[j] < 0
ensures b ==> 0 <= i < v.Length && v[i] < 0 && positive(v[0..i]) {
    i := 0;
    b := false;
    while i < v.Length && !b
    decreases v.Length - i, !b
    invariant i <= v.Length
    invariant !b ==> positive(v[..i])
    invariant b ==> i < v.Length && v[i] < 0 && positive(v[..i]) {
        b := v[i] < 0;
        if !b {
            i := i + 1;
        }
    }
}
