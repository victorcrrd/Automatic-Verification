include "List.dfy"

method replace(l:List, x:int, y:int)
modifies l, l.Repr()

requires l.Valid()
requires forall z | z in l.Repr() :: allocated(z)

ensures l.Valid()

ensures |l.Model()| == |old(l.Model())|
ensures forall i :: 0 <= i < |l.Model()| && old(l.Model())[i] != x ==> l.Model()[i] == old(l.Model())[i];
ensures forall i :: 0 <= i < |l.Model()| && old(l.Model())[i] == x ==> l.Model()[i] == y

ensures l.Iterators() >= old(l.Iterators())

ensures forall z {:trigger z in l.Repr(), z in old(l.Repr())} | z in l.Repr() && z !in old(l.Repr()) :: fresh(z)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall z | z in l.Repr() :: allocated(z) {
    if x == y {
        return;
    }

    var it:ListIterator := l.Begin();
    var elem:int;

    while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant it.Valid()
    invariant l == it.Parent()
    invariant it.Parent().Valid()
    invariant 0 <= it.Index() <= l.Size() == |l.Model()|
    invariant it in l.Iterators()
    invariant |l.Model()| == |old(l.Model())|

    invariant forall i :: it.Index() <= i < |l.Model()| ==> old(l.Model())[i] == l.Model()[i]
    invariant forall i :: 0 <= i < it.Index() && old(l.Model())[i] != x ==> l.Model()[i] == old(l.Model())[i];
    invariant forall i :: 0 <= i < it.Index() && old(l.Model())[i] == x ==> l.Model()[i] == y

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall z {:trigger z in l.Repr(), z in old(l.Repr())} | z in l.Repr() && z !in old(l.Repr()) :: fresh(z)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall z | z in l.Repr() :: allocated(z) {
        if it.Peek() == x {
            it.Set(y);
        }
        elem := it.Next();
    }
}
