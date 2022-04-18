include "Stack.dfy"
include "Queue.dfy"
include "List.dfy"
include "Utils.dfy"

lemma compSeqs<T>(s1:seq<T>, s2:seq<T>, x:T, y:T)
requires |s1| == |s2|
requires [x] + s1 == [y] + s2
ensures x == y && s1 == s2 {
    assert x != y ==> ([x] + s1)[0] == x != y == ([y] + s2)[0];
    assert forall i :: 0 <= i <= |s1| ==> ([x] + s1)[i] == ([y] + s2)[i];
    assert forall i :: 0 <= i < |s1| ==> s1[i] == ([x] + s1)[i+1] == ([y] + s2)[i+1] == s2[i];
}

method fillStack(l:List, s:Stack)
modifies l, l.Repr(), s, s.Repr()
requires l.Valid()
requires s.Valid()
requires forall x :: x in l.Repr() || x in s.Repr() ==> allocated(x)
requires {s} + s.Repr() !! {l} + l.Repr()
requires s.Empty()

ensures l.Valid() && l.Model() == old(l.Model())
ensures s.Valid() && s.Model() == Seq.Rev(l.Model())
ensures {s} + s.Repr() !! {l} + l.Repr()

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)

ensures l.Iterators() >= old(l.Iterators()) {
    var it:ListIterator := l.Begin();
    var elem:int;

    while it.HasNext()
    decreases l.Size() - it.Index()
    invariant l.Valid()
    invariant s.Valid()
    invariant it.Valid()
    invariant l == it.Parent()
    invariant it.Parent().Valid()
    invariant 0 <= it.Index() <= l.Size() == |l.Model()|
    invariant it in l.Iterators()
    invariant l == old(l)
    invariant l.Model() == old(l.Model())
    invariant !it.HasNext() <==> it.Index() == l.Size()

    invariant {s} + s.Repr() !! {l} + l.Repr()
    invariant s.Model() == Seq.Rev(l.Model()[..it.Index()])

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall x | x in s.Repr() :: allocated(x)
    invariant l.Iterators() >= old(l.Iterators())

    invariant l.Model()[..l.Size()] == l.Model(); {
        ghost var sp := s.Model();
        ghost var itp := it.Copy();
        
        elem := it.Next();

        assert itp.Index() + 1 == it.Index() && l.Model()[itp.Index()] == elem;
        assert l.Model()[..itp.Index()] + [elem] == l.Model()[..it.Index()];
        assert sp == Seq.Rev(l.Model()[..itp.Index()]);

        s.Push(elem);

        assert s.Model() == [elem] + sp == [elem] + Seq.Rev(l.Model()[..itp.Index()]);
        Seq.LastRev(l.Model()[..it.Index()]);
        assert [elem] + Seq.Rev(l.Model()[..itp.Index()]) == Seq.Rev(l.Model()[..it.Index()]);
    }
}

method fillQueue(l:List, q:Queue)
modifies l, l.Repr(), q, q.Repr()
requires l.Valid()
requires q.Valid()
requires forall x :: x in l.Repr() || x in q.Repr() ==> allocated(x)
requires {q} + q.Repr() !! {l} + l.Repr()
requires q.Empty()

ensures l.Valid() && l.Model() == old(l.Model())
ensures q.Valid() && q.Model() == l.Model()
ensures {q} + q.Repr() !! {l} + l.Repr()

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)
ensures forall x {:trigger x in q.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
ensures fresh(q.Repr()-old(q.Repr()))
ensures forall x | x in q.Repr() :: allocated(x)

ensures l.Iterators() >= old(l.Iterators()) {
    var it:ListIterator := l.Begin();
    var elem:int;

    while it.HasNext()
    decreases l.Size() - it.Index()
    invariant l.Valid()
    invariant q.Valid()
    invariant it.Valid()
    invariant l == it.Parent()
    invariant it.Parent().Valid()
    invariant 0 <= it.Index() <= l.Size() == |l.Model()|
    invariant it in l.Iterators()
    invariant l == old(l)
    invariant l.Model() == old(l.Model())
    invariant !it.HasNext() <==> it.Index() == l.Size()

    invariant {q} + q.Repr() !! {l} + l.Repr()
    invariant q.Model() == l.Model()[..it.Index()]

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant forall x {:trigger x in q.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall x | x in q.Repr() :: allocated(x)
    invariant l.Iterators() >= old(l.Iterators())

    invariant l.Model()[..l.Size()] == l.Model(); {
        elem := it.Next();
        q.Enqueue(elem);
    }
}

predicate isPalindrome(s:seq<int>) {
    forall i | 0 <= i < |s| :: s[i] == s[|s|-i-1]
}

method palindrome(l:List, s:Stack, q:Queue) returns (b:bool)
modifies l, l.Repr(), s, s.Repr(), q, q.Repr()
requires l.Valid()
requires s.Valid()
requires q.Valid()
requires forall x :: x in l.Repr() || x in s.Repr() || x in q.Repr() ==> allocated(x)
requires {s} + s.Repr() !! {l} + l.Repr()
requires {q} + q.Repr() !! {l} + l.Repr()
requires {s} + s.Repr() !! {q} + q.Repr()
requires s.Empty()
requires q.Empty()

ensures l.Valid() && l.Model() == old(l.Model())
ensures s.Valid()
ensures q.Valid()

ensures b <==> isPalindrome(l.Model())

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
ensures forall x {:trigger x in q.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
ensures fresh(q.Repr()-old(q.Repr()))
ensures forall x | x in q.Repr() :: allocated(x)

ensures l.Iterators() >= old(l.Iterators()) {
    b := true;

    if l.Size() == 0 {
        return;
    }

    assert l.Size() > 0;

    fillStack(l, s);
    fillQueue(l, q);

    assert l.Model() == old(l.Model());

    ghost var ss := s.Model();
    assert ss == Seq.Rev(l.Model());
    Seq.lreverse(l.Model());
    assert forall i | 0 <= i < l.Size() :: Seq.Rev(l.Model())[i] == ss[i] == l.Model()[l.Size()-i-1];

    ghost var qs := q.Model();
    assert qs == l.Model();
    assert forall i | 0 <= i < l.Size() :: qs[i] == l.Model()[i];

    assert (forall i | 0 <= i < l.Size() :: qs[i] == ss[i]) <==> isPalindrome(l.Model());

    var i:int := 0;
    var sElem:int;
    var qElem:int;

    while i < l.Size() && b
    decreases l.Size() - i, b
    invariant l.Valid()
    invariant s.Valid()
    invariant q.Valid()
    invariant 0 <= i <= l.Size() == |l.Model()| == |ss| == |qs|
    invariant |l.Model()| >= |s.Model()| == |q.Model()| == |l.Model()| - i >= 0
    invariant l.Model() == old(l.Model())
    invariant i < l.Size() ==> s.Model() == ss[i..] && s.Model() != []
    invariant i < l.Size() ==> q.Model() == qs[i..] && q.Model() != []
    invariant b <==> ss[..i] == qs[..i]
    invariant {s} + s.Repr() !! {l} + l.Repr()
    invariant {q} + q.Repr() !! {l} + l.Repr()
    invariant {s} + s.Repr() !! {q} + q.Repr()
    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() && x !in old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
    invariant forall x {:trigger x in q.Repr(), x in old(q.Repr())} | x in q.Repr() && x !in old(q.Repr()) :: fresh(x)
    invariant fresh(q.Repr()-old(q.Repr()))
    invariant forall x | x in q.Repr() :: allocated(x)
    invariant l.Iterators() >= old(l.Iterators()) {
        assert b <==> ss[..i] == qs[..i];

        sElem := s.Pop();
        qElem := q.Dequeue();

        assert sElem == ss[i];
        assert qElem == qs[i];

        if sElem != qElem {
            b := false;
            assert b <==> ss[..i+1] == qs[..i+1];
        }

        i := i + 1;
    }
}
