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
