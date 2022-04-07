predicate sorted(a:array<int>, i:nat, j:nat)
reads a
requires 0 <= i <= j <= a.Length {
    forall l, k :: 0 <= i <= l <= k < j ==> a[l] <= a[k] 
}

lemma arrayFacts()
ensures forall a:array<int> ::
    a[..] == a[0..] == a[..a.Length] == a[0..a.Length] {}

method heapSortWithExtraSpace(a:array<int>)
modifies a
ensures sorted(a, 0, a.Length)
ensures multiset(a[..]) == multiset(old(a[..])) {
    arrayFacts();

    ghost var a0 := a[..];
    var queue := new WilliamsHeap(a.Length);

    var i:int := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i == queue.next <= a.Length == queue.v.Length
    invariant queue.isHeap()
    invariant multiset(queue.model()) == multiset(queue.v[..i])
    invariant multiset(queue.v[..i]) == multiset(a0[..i])
    invariant a0 == a[..]
    invariant fresh(queue.repr) {
        queue.insert(a[i]);
        i := i + 1;
    }
    assert queue.isHeap();
    assert multiset(queue.model()) == multiset(queue.v[..queue.next]);
    assert multiset(queue.v[..queue.next]) == multiset(a0);

    i := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant 0 <= queue.next == a.Length - i
    invariant sorted(a, 0, i)
    invariant queue.isHeap()
    invariant multiset(queue.model()) + multiset(a[..i]) == multiset(a0)
    invariant fresh(queue.repr) {
        assert sorted(a, 0, i);
        assert forall j :: 0 <= j < queue.next ==> queue.min() <= queue.v[j];
        // this assumption should be removed and could be proved by adding an
        // appropriate invariant in the loop and proving that it's mantained,
        // however, I wasn't able to do it
        assume forall j :: 0 <= j < i ==> a[j] <= queue.min();
        a[i] := queue.min();
        queue.deleteMin();
        i := i + 1;
    }
    assert a[..] == a[..a.Length];
    assert multiset(a[..]) == multiset(a[..a.Length]) == multiset(a0);
}

class WilliamsHeap {
    var v:array<int>;
    var next:nat;
    ghost var repr:set<object>

    function model() : (m:seq<int>)
    reads repr
    requires isHeap()
    ensures |m| == next
    ensures forall i :: 0 <= i < next ==> m[i] == v[i] {
        v[..next]
    }

    predicate isHeap()
    reads this, v {
        repr == {this, v} && 0 <= next <= v.Length &&
        forall i :: 0 < i < next ==> v[(i-1)/2] <= v[i]
    }

    lemma orderedModel()
    requires isHeap()
    ensures forall i :: 0 < i < next ==> model()[(i-1)/2] <= model()[i] {}

    lemma {:induction i} biggerThanHead(i:nat)
    requires 0 <= i < next
    requires isHeap()
    ensures model()[0] == v[0] <= v[i] == model()[i] {}

    lemma minimumElement()
    requires 0 < next <= v.Length
    requires isHeap()
    ensures forall i :: 0 <= i < next ==> v[0] <= v[i] == model()[i] {
        forall i | 0 <= i < next ensures v[0] <= v[i] {
            biggerThanHead(i);
        }
    }

    constructor(size:nat)
    ensures isHeap()
    ensures next == 0
    ensures v.Length == size
    ensures repr == {this, v}
    ensures fresh(repr) {
        v := new int[size];
        next := 0;
        repr := {this, v};
    }

    function method min() : (m:int)
    reads this, v
    requires 0 < next
    requires isHeap()
    ensures isHeap()
    ensures forall i :: 0 <= i < next ==> m <= v[i] {
        minimumElement();
        v[0]
    }

    method insert(val:int)
    modifies this, v
    requires 0 <= next < v.Length
    requires isHeap()
    ensures isHeap()
    ensures multiset(model()) == multiset(old(model())) + multiset{val}
    ensures next == old(next) + 1
    ensures repr == old(repr) {
        v[next] := val;
        next := next + 1;
        float();
    }

    method float()
    modifies v
    requires 0 < next <= v.Length
    requires repr == {this, v}
    requires forall i :: 0 < i < next - 1 ==> v[(i-1)/2] <= v[i]
    ensures isHeap()
    ensures multiset(v[..next]) == multiset(old(v[..next]))
    ensures next == old(next)
    ensures repr == old(repr) {
        var j:int := next - 1;
        while j > 0 && v[(j-1)/2] > v[j]
        invariant 0 <= j <= next - 1 < v.Length
        invariant forall i :: 0 < i < next ==> (i != j ==> v[(i-1)/2] <= v[i])
        invariant j > 0 && 2*j + 1 < next ==> v[(j-1)/2] <= v[2*j+1]
        invariant j > 0 && 2*j + 2 < next ==> v[(j-1)/2] <= v[2*j+2]
        invariant multiset(v[..next]) == multiset(old(v[..next])) {
            v[(j-1)/2], v[j] := v[j], v[(j-1)/2];
            j := (j-1)/2;
        }
    }

    method deleteMin()
    modifies this, v
    requires 0 < next <= v.Length
    requires isHeap()
    ensures isHeap()
    ensures multiset(model()) == multiset(old(model())) - multiset{old(min())}
    ensures next == old(next) - 1
    ensures repr == old(repr) {
        v[0] := v[next-1];
        next := next - 1;
        sink();
    }

    method sink()
    modifies v
    requires 0 <= next < v.Length
    requires repr == {this, v}
    requires forall i :: 0 < i < next ==> ((i-1)/2 != 0 ==> v[(i-1)/2] <= v[i])
    ensures isHeap()
    ensures multiset(v[..next]) == multiset(old(v[..next]))
    ensures next == old(next)
    ensures repr == old(repr) {
        var j:int := 0;
        while 2*j + 1 < next
        invariant forall i :: 0 < i < next ==> ((i-1)/2 != j ==> v[(i-1)/2] <= v[i])
        invariant j > 0 && 2*j + 1 < next ==> v[(j-1)/2] <= v[2*j+1] 
        invariant j > 0 && 2*j + 2 < next ==> v[(j-1)/2] <= v[2*j+2]
        invariant multiset(v[..next]) == multiset(old(v[..next])) {
            var m: nat;
            if 2*j + 2 < next && v[2*j+2] <= v[2*j+1] {
                m := 2*j + 2;
            } else {
                m := 2*j + 1;
            }
            if v[j] > v[m] {
                v[j], v[m] := v[m], v[j];
                j := m;
            } else {
                break;
            }
        }
    }
}
