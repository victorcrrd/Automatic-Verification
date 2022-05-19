// Exercise 1: [6pts]
// We want to check if an array w is a "slipped version" of another array v of
// the same length. We say that w is a "slipped version" of v at index k if
// v[0] == w[k] and the sequence of elements are the same in both arrays
// considering w as circular: v[1] == w[k+1], v[2] == w[k+2], etc.
// As example: given v = [2,5,1,6,8] and w= [6,8,2,5,1], w is a slipped version
// of v at index 2 as v[0] == w[2], v[1] == w[3], v[2] == w[4], v[3] == w[0] and
// v[4] == w[1].
// We will solve the problem for arrays where all the elements are different.

// 1. [0.5pts] Define the following predicates 
predicate different(v:array<int>)
reads v {
    forall i, j :: 0 <= i < j < v.Length ==> v[i] != v[j]
}

predicate slipped(v:array<int>, w:array<int>, k:int)
requires 0 <= k < v.Length == w.Length
reads v, w {
    forall i :: 0 <= i < v.Length ==> v[i] == w[(k+i)%w.Length]
}

predicate slippedUpTo(v:array<int>, w:array<int>, k:int, i:int)
requires 0 <= k < v.Length == w.Length
requires 0 <= i <= v.Length == w.Length
reads v, w {
    forall j :: 0 <= j < i ==> v[j] == w[(k+j)%w.Length]
}

lemma slippedUpToTheEnd(v:array<int>, w:array<int>, k:int)
requires 0 <= k < v.Length == w.Length
ensures slipped(v, w, k) <==> slippedUpTo(v, w, k, v.Length) {}

// 2. [1.5pts] Prove the following lemmas
// 2.1. If v[0] is not in w then w is not a slipped version of v for any k
lemma necessarySlippedCondition(v:array<int>, w:array<int>)
requires 0 < v.Length == w.Length
ensures forall kp :: 0 <= kp < v.Length ==>
    (slipped(v, w, kp) ==> v[0] == w[kp]) {}

lemma firstMustAppear(v:array<int>, w:array<int>)
requires 0 < v.Length == w.Length
requires forall k :: 0 <= k < v.Length ==> v[0] != w[k]
ensures forall k :: 0 <= k < v.Length ==> !slipped(v, w, k) {
    necessarySlippedCondition(v, w);
}
 
// 2.2. If v[0] == w[k] but w is not a slipped version of v at index k then
// there is no other possibility of being a slipped version of v
lemma onlyPossibility(v:array<int>, w:array<int>, k:int)
requires 0 < v.Length == w.Length
requires 0 <= k < v.Length
requires different(v)
requires different(w)
requires v[0] == w[k]
requires !slipped(v, w, k)
ensures forall kp :: 0 <= kp < v.Length ==> !slipped(v, w, kp) {
    necessarySlippedCondition(v, w);
    assert forall i :: 0 <= i < v.Length && i != k ==> v[0] == w[k] != w[i];
    assert forall kp :: 0 <= kp < v.Length && kp != k ==> !slipped(v, w, kp);
}
   
// 3. [1pts] Write the postcondition of method mslipped, i.e., b is true if and
// only if w is a slipped version of v; if b is true then w is a slipped version
// of v from index k; and if b is false k must b v.Length

// 4. [3pts] Implement and verify the method that given two arrays v and w
// containing different elements checks if w is a slipped version of v. First
// write a loop for looking for v[0] in w. If it does not appear then w cannot
// be a slipped version of v. Otherwise if v[0] == w[i], write a loop to check
// circularly the rest of elements. Use the previous lemmas to verify

method mslipped(v:array<int>, w:array<int>) returns (b:bool, k:int)
requires 0 < v.Length == w.Length
requires different(v)
requires different(w)
ensures b <==> exists kp :: 0 <= kp < v.Length && slipped(v, w, kp)
ensures b ==> (0 <= k < v.Length && slipped(v, w, k))
ensures !b ==> k == v.Length {
    // First we want to find a candidate for the slipped index k, so we
    // iterate until we find a k such that v[0] == w[k]. If such k doesn't
    // exist, then we know that b must be false.
    k := 0;
    while k < v.Length && v[0] != w[k]
    decreases v.Length - k
    invariant 0 <= k <= v.Length
    invariant forall i :: 0 <= i < k ==> v[0] != w[i] {
        k := k + 1;
    }
    assert forall i :: 0 <= i < k ==> v[0] != w[i];
    assert k < v.Length ==> v[0] == w[k];
    if k == v.Length {
        assert forall i :: 0 <= i < v.Length ==> v[0] != w[i];
        firstMustAppear(v, w);
        b := false;
        return;
    }

    // We know that if w is a slipped version of v, then it has to be of index k
    assert k < v.Length && v[0] == w[k];
    assert forall kp :: 0 <= kp < v.Length && kp != k ==> !slipped(v, w, kp);

    // Now we want to check whether or not w is a slipped version of v of index
    // k, to do that we simply check if v[i] == w[(k+i)%w.Length] for all
    // possible index i
    b := true;
    var i:int := 0;
    while i < v.Length && b
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant b <==> slippedUpTo(v, w, k, i)
    invariant !b ==> (i > 0 && slippedUpTo(v, w, k, i-1)) {
        if v[i] != w[(k+i)%w.Length] {
            b := false;
        }
        i := i + 1;
    }
    assert b ==> slippedUpTo(v, w, k, v.Length);
    slippedUpToTheEnd(v, w, k);
    if !b {
        k := v.Length;
        return;
    }
}
