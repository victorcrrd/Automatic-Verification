include "ExerciseSumElems.dfy"

function sumM(m:multiset<int>):int
decreases m {
    if m == multiset{} then 0
    else var x :| x in m; x + sumM(m - multiset{x})
}

lemma sumElementAndMultiset(m:multiset<int>, x:int)
requires x in m
ensures sumM(m) == x + sumM(m - multiset{x})

lemma sumMultisets(m:multiset<int>, n:multiset<int>)
decreases m
ensures sumM(m+n) == sumM(m) + sumM(n) {
    if m == multiset{} {
        assert m+n == n;
    } else {
        var x :| x in m;
        assert x in m;
        assert m - multiset{x} + multiset{x} == m;
        assert m - multiset{x} + n + multiset{x} == m + n;
        assert m + n - multiset{x} + multiset{x} == m + n;
        calc == {
            sumM(m) + sumM(n);
            { sumMultisets(m - multiset{x}, multiset{x}); }
            x + sumM(m - multiset{x}) + sumM(n);
            { sumMultisets(m - multiset{x}, n); }
            x + sumM(m - multiset{x} + n);
            { assert m - multiset{x} + n == m + n - multiset{x}; }
            x + sumM(m + n - multiset{x});
            { sumElementAndMultiset(m + n - multiset{x} + multiset{x}, x); }
            sumM(m+n);
        }
    }
}

function sumSM(s:seq<int>):int {
    sumM(multiset(s))
}

function sumVM(v:array<int>, c:int, f:int):int
requires 0 <= c <= f <= v.Length
reads v {
    sumSM(v[c..f])
}

lemma {:induction m} sumOne(m:multiset<int>, x:int)
decreases m
requires x in m
ensures sumM(m) == x + sumM(m - multiset{x}) {
    var y :| y in m && sumM(m) == y + sumM(m - multiset{y});
    if x == y {
        return;
    } else {
        calc == {
            sumM(m);
            y + sumM(m - multiset{y});
            { sumOne(m - multiset{y}, x); }
            y + x + sumM(m - multiset{y} - multiset{x});
            { assert m - multiset{x} - multiset{y} == m - multiset{y} - multiset{x}; }
            x + y + sumM(m - multiset{x} - multiset{y});
			{ sumOne(m - multiset{x}, y); }
			x + sumM(m - multiset{x});
        }
    }
}

lemma {:induction m, n} sumByParts(m:multiset<int>, n:multiset<int>)
decreases m, n
ensures sumM(m + n) == sumM(m) + sumM(n) {
    if m == multiset{} {
        assert m + n == n;
    } else if n == multiset{} {
        assert m + n == m;
    } else {
        var x :| x in m;
        sumByParts(m - multiset{x}, n);
        assert (m - multiset{x}) + n == (m + n) - multiset{x};
        assert sumM((m - multiset{x}) + n) == sumM((m + n) - multiset{x});
        sumOne(m, x);
        sumOne(m + n, x);
    }
}

lemma singletonSubsequence(s:seq<int>)
ensures forall i :: 0 <= i < |s| ==> multiset(s[i..i+1]) == multiset{s[i]} {}

lemma sequencesAsMultisets(s:seq<int>)
ensures multiset(s) == multiset(s[0..|s|]) {
    assert s == s[0..|s|];
}

lemma subsequencesAsMultisetsRight(s:seq<int>)
requires s != []
ensures multiset(s) == multiset(s[..|s|-1]) + multiset{s[|s|-1]}
ensures multiset(s) - multiset{s[|s|-1]} == multiset(s[..|s|-1]) {
    assert s == s[..|s|-1] + s[|s|-1..|s|];
    singletonSubsequence(s);
    sequencesAsMultisets(s);
}

lemma subsequencesAsMultisetsLeft(s:seq<int>)
requires s != []
ensures multiset(s) == multiset{s[0]} + multiset(s[1..])
ensures multiset(s) - multiset{s[0]} == multiset(s[1..]) {
    assert s == s[0..1] + s[1..];
    singletonSubsequence(s);
    sequencesAsMultisets(s);
}

lemma elementsInASequence(s:seq<int>)
requires s != []
ensures forall i :: 0 <= i < |s| ==> s[i] in multiset(s) {}

lemma {:induction s} sumS(s:seq<int>)
decreases s
ensures sumSM(s) == sumL(s)
ensures sumSM(s) == sumR(s) {
    assert s == s[0..|s|];
    equalSum(s, 0, |s|);
    if s != [] {
        SeqFacts<int>();
        subsequencesAsMultisetsRight(s);
        elementsInASequence(s);
        calc == {
            sumR(s);
            sumR(s[..|s|-1]) + s[|s|-1];
            { sumS(s[..|s|-1]); }
            sumSM(s[..|s|-1]) + s[|s|-1];
            { sumOne(multiset(s), s[|s|-1]); }
            sumSM(s);
        }
    }
}

lemma decomposeM(v:array<int>, c:int, f:int)
requires 0 <= c < f <= v.Length
decreases f-c
ensures sumVM(v, c, f) == sumVM(v, c, f-1) + v[f-1]
ensures sumVM(v, c, f) == v[c] + sumVM(v, c+1, f) {
    subsequencesAsMultisetsRight(v[c..f]);
    subsequencesAsMultisetsLeft(v[c..f]);
    calc == {
        sumVM(v, c, f);
        sumSM(v[c..f]);
        sumM(multiset(v[c..f]));
        { assert multiset(v[c..f]) == multiset(v[c..f-1]) + multiset{v[f-1]}; }
        sumM(multiset(v[c..f-1]) + multiset{v[f-1]});
        { sumByParts(multiset(v[c..f-1]), multiset{v[f-1]}); }
        sumM(multiset(v[c..f-1])) + v[f-1];
        sumSM(v[c..f-1]) + v[f-1];
        sumVM(v, c, f-1) + v[f-1];
    }
    calc == {
        sumVM(v, c, f);
        sumSM(v[c..f]);
        sumM(multiset(v[c..f]));
        { assert multiset(v[c..f]) == multiset(v[c+1..f]) + multiset{v[c]}; }
        sumM(multiset{v[c]} + multiset(v[c+1..f]));
        { sumByParts(multiset{v[c]}, multiset(v[c+1..f])); }
        v[c] + sumM(multiset(v[c+1..f]));
        v[c] + sumSM(v[c+1..f]);
        v[c] + sumVM(v, c+1, f);
    }
    /*calc == {
        sumVM(v, c, f);
        sumSM(v[c..f]);
        { sumS(v[c..f]); }
        sumR(v[c..f]);
        { assert v[c..f][..f-c-1] == v[c..f-1]; }
        sumR(v[c..f-1]) + v[f-1];
        { sumS(v[c..f-1]); }
        sumSM(v[c..f-1]) + v[f-1];
        sumVM(v, c, f-1) + v[f-1];
    }
    calc == {
        sumVM(v, c, f);
        sumSM(v[c..f]);
        { sumS(v[c..f]); }
        sumL(v[c..f]);
        v[c] + sumL(v[c+1..f]);
        { sumS(v[c+1..f]); }
        v[c] + sumSM(v[c+1..f]);
        v[c] + sumVM(v, c+1, f);
    }*/
}

lemma {:induction s,r} sumElemsS(s:seq<int>,r:seq<int>)
requires multiset(s) == multiset(r)
ensures sumSM(s) == sumSM(r) {}

lemma SeqFacts<T>()
    ensures forall s:seq<T> | |s| >= 1 :: |s[1..|s|]| == |s|-1;
    ensures forall s:seq<T>, i, j | 0 <= i <= j <= |s| :: |s[i..j]| == j-i
    ensures forall s:seq<T>, i, j | 0 <= i < j <= |s| :: s[i..j][..(j-i)-1] == s[i..j-1]
    ensures forall s:seq<T>, i, j, k | 0 <= i <= k <= j <= |s| :: multiset(s[i..k]) + multiset(s[k..j]) == multiset(s[i..j]) {
        forall s : seq<T>, i, j, k | 0 <= i <= k <= j <= |s|
        ensures multiset(s[i..k]) + multiset(s[k..j]) == multiset(s[i..j]) {
            assert s[i..k] + s[k..j] == s[i..j];
        }
    }

lemma ArrayFactsM<T>()
    ensures forall v:array<int>, i, j | 0 <= i < j <= v.Length :: sumVM(v, i, j) == sumVM(v, i, j - 1) + v[j-1]
    ensures forall v:array<int>, i, j | 0 <= i < j <= v.Length :: sumVM(v, i, j) == v[i] + sumVM(v, i + 1, j)
    ensures forall v:array<int>, i, j, k | 0 <= i <= k <= j <= v.Length :: sumVM(v, i, j) == sumVM(v, i, k) + sumVM(v, k, j) {
        SeqFacts<int>();

        forall v:array<int>, i, j | 0 <= i < j <= v.Length
        ensures sumVM(v, i, j) == sumVM(v, i, j - 1) + v[j-1] {
            decomposeM(v, i, j);
        }

        forall v:array<int>, i, j | 0 <= i < j <= v.Length
        ensures sumVM(v, i, j) == v[i] + sumVM(v, i + 1, j) {
            decomposeM(v, i, j);
        }

        forall v:array<int>, i, j, k | 0 <= i <= k <= j <= v.Length
        ensures sumVM(v, i, j) == sumVM(v, i, k) + sumVM(v, k, j) {
            assert multiset(v[i..j]) == multiset(v[i..k]) + multiset(v[k..j]);
            sumMultisets(multiset(v[i..k]), multiset(v[k..j]));
        }
    }

/*lemma ArrayFactsM<T>()
    ensures forall v:array<T> :: v[..v.Length] == v[..];
	ensures forall v:array<T> :: v[0..] == v[..];
    ensures forall v:array<T> :: v[0..v.Length] == v[..];
	ensures forall v:array<T> :: |v[0..v.Length]| == v.Length;
    ensures forall v:array<T> | v.Length >= 1 :: |v[1..v.Length]| == v.Length-1;
    ensures forall v:array<T> :: forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
    ensures forall v:array<int>, i, j | 0 <= i <= j <= v.Length :: sumR(v[i..j]) == sumL(v[i..j])
    ensures forall v:array<int>, i, j | 0 <= i < j <= v.Length :: sumVM(v,i,j) == sumVM(v,i,j-1) + v[j-1]
    ensures forall v:array<int>, i, j | 0 <= i < j <= v.Length :: sumVM(v,i,j) == v[i] + sumVM(v,i+1,j) 
    ensures forall v:array<int>, i, j | 0 <= i <= j <= v.Length :: sumSM(v[i..j]) == sumR(v[i..j])
    ensures forall v:array<int>, i, j | 0 <= i <= j <= v.Length :: sumSM(v[i..j]) == sumL(v[i..j])
    ensures forall v:array<int>, i, j | 0 <= i <= j <= v.Length :: sumV(v,i,j) == sumVM(v,i,j) == sumL(v[i..j]) == sumR(v[i..j]) == sumSM(v[i..j])
    ensures forall v:array<int>, i, j, k | 0 <= i <= k <= j <= v.Length :: sumVM(v,i,j) == sumVM(v,i,k) + sumVM(v,k,j) {
        equalSumV();
        SeqFacts<int>();
        forall v:array<int>, i, j | 0 <= i < j <= v.Length
        ensures sumVM(v,i,j) == sumVM(v,i,j-1) + v[j-1] {
            decomposeM(v,i,j);
        }

        forall v:array<int>, i, j | 0 <= i < j <= v.Length
        ensures sumVM(v,i,j) == v[i] + sumVM(v,i+1,j) {
            decomposeM(v,i,j);
        }

        forall s:seq<int>
        ensures sumSM(s) == sumR(s)
        ensures sumSM(s) == sumL(s) {
            sumS(s);
        }
}*/

method sumElemsE(v:array<int>) returns (sum:int)
ensures sum == sumVM(v, 0, v.Length) {
    ArrayFactsM<int>();
    sum := 0;
    var i:int := 0;
    var m:int := v.Length/2;
    while i < m
    decreases m - i
    invariant 0 <= i <= m
    invariant sum == sumVM(v, 0, i) {
        sum := sum + v[i];
        i := i + 1;
    }
    assert sum == sumVM(v, 0, m);
    var aux: int := 0;
    assert i == m;
    while i < v.Length
    decreases v.Length - i
    invariant m <= i <= v.Length
    invariant aux == sumVM(v, m, i) {
        aux := aux + v[i];
        i := i + 1;
    }
    assert aux == sumVM(v, m, v.Length);
    sum := sum + aux;
}
