predicate allEqual(s:seq<int>) {
    forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    // forall i, j :: 0 <= i <= j < |s| ==> s[i] == s[j]
    // forall i :: 0 < i < |s| ==> s[i-1] == s[i]
    // forall i :: 0 <= i < |s|-1 ==> s[i] == s[i+1]
}

// Ordered indexes
lemma equivalenceNoOrder(s:seq<int>)
ensures allEqual(s) <==> forall i, j :: 0 <= i <= j < |s| ==> s[i] == s[j] {}

// All equal to first
lemma equivalenceEqualToFirst(s:seq<int>)
requires s != []
ensures allEqual(s) <==> forall i :: 0 <= i < |s| ==> s[0] == s[i] {}

// All equal to last
lemma equivalenceEqualToLast(s:seq<int>)
requires s != []
ensures allEqual(s) <==> forall i :: 0 <= i < |s| ==> s[|s|-1] == s[i] {}

// Subsequences starting at the beginning
lemma subsequencesLeftAllEqual(s:seq<int>)
decreases |s|
ensures allEqual(s) <==> forall i :: 0 <= i <= |s| ==> allEqual(s[..i]) {
    if |s| > 0 {
        calc ==> {
            forall i :: 0 <= i <= |s| ==> allEqual(s[..i]);
            { assert s == s[..|s|]; }
            allEqual(s);
        }
        calc ==> {
            allEqual(s);
            allEqual(s[..|s|-1]) && forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1];
        }
    }
}

// Subsequences ending at the end
lemma subsequencesRightAllEqual(s:seq<int>)
decreases |s|
ensures allEqual(s) <==> forall i :: 0 <= i <= |s| ==> allEqual(s[i..]) {
    if |s| > 0 {
        calc ==> {
            forall i :: 0 <= i <= |s| ==> allEqual(s[i..]);
            { assert s == s[0..]; }
            allEqual(s);
        }
        calc ==> {
            allEqual(s);
            allEqual(s[1..]) && forall i :: 0 <= i < |s| ==> s[0] == s[i];
        }
    }
}

// Subsequences
lemma subsequencesAllEqual(s:seq<int>)
decreases |s|
ensures allEqual(s) <==> forall i, j :: 0 <= i <= j <= |s| ==> allEqual(s[i..j]) {
    if |s| > 1 {
        calc ==> {
            forall i, j :: 0 <= i <= j <= |s| ==> allEqual(s[i..j]);
            { assert s == s[0..|s|]; }
            allEqual(s);
        }
    }
}

// Contiguous are equal
lemma equivalenceContiguous(s:seq<int>)
ensures allEqual(s) <==> forall i :: 0 <= i < |s|-1 ==> s[i] == s[i+1] {
    if |s| > 1 {
        calc ==> {
            allEqual(s);
            forall i :: 0 <= i < |s|-1 && 0 < i+1 < |s| ==> s[i] == s[i+1];
        }
        calc ==> {
            forall i :: 0 <= i < |s|-1 ==> s[i] == s[i+1];
            { equivalenceContiguous(s[..|s|-1]); }
            allEqual(s[..|s|-1]) && s[|s|-2] == s[|s|-1];
            allEqual(s);
        }
    }
}

method mallEqual1(v:array<int>) returns (b:bool)
ensures b == allEqual(v[..]) {
    var i:int := 0;
    b := true;
    while i < v.Length && b
    decreases v.Length - i
    invariant i <= v.Length
    invariant b == allEqual(v[..i]) {
        b := v[i] == v[0];
        i := i + 1;
    }
}

method mallEqual2(v:array<int>) returns (b:bool)
ensures b == allEqual(v[..]) {
    var i:int := 0;
    b := true;
    while i < v.Length && v[i] == v[0]
    decreases v.Length - i
    invariant i <= v.Length
    invariant allEqual(v[..i]) {
        i := i + 1;
    }
    b := i == v.Length;
}

method mallEqual3(v:array<int>) returns (b:bool)
ensures b == allEqual(v[..]) {
    equivalenceContiguous(v[..]);
    var i:int := 0;
    b := true;
    if v.Length > 0 {
        while i < v.Length-1 && v[i] == v[i+1]
        decreases v.Length - i
        invariant i < v.Length
        invariant forall j :: 0 <= j < i ==> v[j] == v[j+1] {
            i := i + 1;
        }
        b := i == v.Length-1;
    }
}

method mallEqual4(v:array<int>) returns (b:bool)
ensures b == allEqual(v[..]) {
    equivalenceContiguous(v[..]);
    var i:int := 0;
    b := true;
    if v.Length > 0 {
        while i < v.Length-1 && b
        decreases v.Length - i
        invariant i < v.Length
        invariant b == forall j :: 0 <= j < i ==> v[j] == v[j+1] {
            b := v[i] == v[i+1];
            i := i + 1;
        }
    }
}

method mallEqual5(v:array<int>) returns (b:bool)
ensures b == allEqual(v[..]) {
    var i:int := 0;
    b := true;
    while i < v.Length && b
    decreases v.Length - i, b
    invariant i <= v.Length
    invariant b ==> allEqual(v[..i])
    invariant !b ==> !allEqual(v[..]) {
        if v[i] != v[0] {
            b := false;
        } else {
            i := i + 1;
        }
    }
}
