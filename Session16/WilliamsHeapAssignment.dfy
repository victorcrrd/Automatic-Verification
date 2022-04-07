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
    assert queue.isHeap();
    assert fresh(queue.repr);

    var i:int := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i == queue.next <= a.Length == queue.v.Length
    invariant queue.model == a0[..i] == a[..i]
    invariant fresh(queue.repr)
    invariant queue.isHeap() {
        queue.insert(a[i]);
        i := i + 1;
    }
    assert queue.model == a0 == a[..];
    assert multiset(queue.model) == multiset(a0) == multiset(a[..]);
    assert queue.isHeap();

    i := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant 0 <= queue.next == a.Length - i
    invariant sorted(a, 0, i)
    invariant multiset(a0) == multiset(a[..])
    invariant multiset(queue.model) + multiset(a[..i]) == multiset(a0)
    invariant fresh(queue.repr)
    invariant queue.isHeap()
    {
        a[i] := queue.min();
        queue.deleteMin();
        i := i + 1;
    }
}

class WilliamsHeap {
    var v:array<int>;
    var next:nat;
    ghost var repr:set<object>
    // we could have also defined the model as a function that is equal to the
    // sequence given by v[0..next], so that we wouldn't have to re-compute its
    // value on each method
    ghost var model:seq<int>

    predicate isHeap()
    reads this, v {
        repr == {this, v} &&
        0 <= next == |model| <= v.Length &&
        (forall i :: 0 <= i < next ==> v[i] == model[i]) &&
        (forall i :: 0 < i < next ==> v[(i-1)/2] <= v[i])
    }

    lemma orderedModel()
    requires isHeap()
    ensures forall i :: 0 < i < next ==> model[(i-1)/2] <= model[i] {}

    lemma {:induction i} biggerThanHead(i:nat)
    requires 0 <= i < next
    requires isHeap()
    ensures model[0] == v[0] <= v[i] == model[i] {}

    lemma minimumElement()
    requires 0 < next <= v.Length
    requires isHeap()
    ensures forall i :: 0 <= i < next ==> model[0] == v[0] <= v[i] == model[i] {
        forall i | 0 <= i < next ensures v[0] <= v[i] {
            biggerThanHead(i);
        }
    }

    constructor(size:nat)
    ensures isHeap()
    ensures next == 0
    ensures v.Length == size
    ensures repr == {this, v}
    ensures model == []
    ensures fresh(repr) {
        v := new int[size];
        next := 0;
        repr := {this, v};
        model := [];
    }

    function method min() : (m:int)
    reads repr
    requires 0 < next
    requires isHeap()
    ensures isHeap()
    ensures forall i :: 0 <= i < next ==> m <= v[i] {
        minimumElement();
        v[0]
    }

    method insert(val:int)
    modifies v
    requires 0 <= next < v.Length
    requires isHeap()
    ensures isHeap()
    ensures next == old(next) + 1
    ensures repr == old(repr)

    method deleteMin()
    modifies v
    requires 0 < next <= v.Length
    requires isHeap()
    ensures isHeap()
    ensures next == old(next) - 1
    ensures repr == old(repr)
}

/*predicate sorted(a:array<int>, i:nat, j:nat)
requires 0 <= i <= j <= a.Length {
    forall l, k :: 0 <= i <= l <= k < j ==> a[l] <= a[k] 
}

method heapSortWithExtraSpace(a:array<int>)
modifies a {
    ghost var a0 := a[0..a.Length];
    var queue := new WilliamsHeap(a.Length);

    var i:int := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant multiset(queue.model) == multiset(a[0..i])
    invariant queue.next == i
    invariant queue.isHeap(0)
    {
        queue.insert(a[i]);
        i := i + 1;
    }
    assert queue.next == a.Length;
    assert multiset(queue.model) == multiset(a[0..a.Length]);
    assert queue.isHeap(0);

    i := 0;
    while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length == queue.next
    invariant sorted(a, 0, i)
    invariant queue.isHeap(0)
    {
        a[i] := queue.min();
        queue.deleteMin();
        i := i + 1;
    }

    assert sorted(a, 0, a.Length);
}

class WilliamsHeap {
    var v:array<int>;
    var next:nat;
    ghost var repr:set<object>;
    ghost var model:seq<int>;

    // v[h..next) is a minimum heap
    predicate isHeap(h:int)
    reads this, v
    requires 0 <= h <= v.Length {
        this in repr && v in repr && 0 <= next <= v.Length &&
        |model| == next && (forall i :: 0 <= i < next ==> v[i] == model[i]) &&
        (forall i :: 2*h < i < next ==> v[(i-1)/2] <= v[i])
    }

    lemma orderedModel(h:int)
    requires 0 <= h <= v.Length
    requires isHeap(h)
    ensures forall i :: 2*h < i < next ==> model[(i-1)/2] <= model[i] {}

    constructor(size:nat)
    ensures isHeap(0)
    ensures v.Length == size
    ensures next == 0
    ensures fresh(repr) {
        v := new int[size];
        next := 0;
        repr := {this, v};
        model := [];
    }

    lemma {:induction i} biggerThanHead(i:nat)
    requires 0 <= i < next
    requires isHeap(0)
    ensures v[0] <= v[i] {}

    lemma minimumElement()
    requires 0 < next <= v.Length
    requires isHeap(0)
    ensures forall i :: 0 <= i < next ==> model[0] == v[0] <= v[i] == model[i] {
        orderedModel(0);
        forall i | 0 <= i < next ensures v[0] <= v[i] {
            biggerThanHead(i);
        }
    }

    function method min() : (m:int)
    reads this, v
    requires 0 < next
    requires isHeap(0)
    ensures forall i :: 0 <= i < next ==> m <= v[i] {
        minimumElement();
        v[0]
    }

    method insert(val:int)
    modifies this, v
    requires 0 <= next < v.Length
    requires isHeap(0)
    ensures isHeap(0)
    ensures next == old(next) + 1
    ensures repr == old(repr)
    {
        v[next] := val;
        next := next + 1;
        float(val);
    }

    method float(val:int)
    modifies v
    requires 0 < next <= v.Length
    requires this in repr && v in repr
    requires forall i :: 0 < i < next - 1 ==> v[(i-1)/2] <= v[i]
    ensures isHeap(0)
    ensures repr == old(repr)

    method deleteMin()
    modifies this, v
    requires 0 < next <= v.Length
    requires isHeap(0)
    ensures isHeap(0)
    ensures next == old(next) - 1
    ensures repr == old(repr)
    {
        v[0] := v[next - 1];
        next := next - 1;
        sink();
    }

    method sink()
    modifies v
    requires 0 <= next < v.Length
    requires this in repr && v in repr
    requires forall i :: 0 < i < next ==> (i-1)/2 != 0 ==> v[(i-1)/2] <= v[i]
    ensures isHeap(0)
    ensures repr == old(repr)
}*/

/*class WilliamsHeap {

    method sink(s:nat)
    modifies v
    requires 0 <= s <= next <= v.Length
    requires this in repr && v in repr
    requires forall i | 0 < i < next :: (i-1)/2 != s ==> v[(i-1)/2] <= v[i]
    ensures isHeap(s)
    ensures repr == old(repr) {
        var j := s;
        while 2*j + 1 < next
        decreases next - 2*j - 1
        invariant forall k | 2*s + 1 <= k < next :: (k-1)/2 != j ==> v[(k-1)/2] <= v[k]
        invariant j >= 2*s + 1 && 2*j + 1 < next ==> v[(j-1)/2] <= v[2*j + 1]
        invariant j >= 2*s + 1 && 2*j + 2 < next ==> v[(j-1)/2] <= v[2*j + 2] {
            var m:nat;
            if 2*j + 2 < next && v[2*j + 2] <= v[2*j + 1] {
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

method heapsortWithExtraSpace(a:array<int>)
modifies a {
    var queue := new WilliamsHeap(a.Length);
    var i := 0;
    while i < a.Length
    decreases a.Length - i
    invariant i <= a.Length
    invariant queue.isHeap(0) {
        queue.insert(a[i]);
        i := i + 1;
    }
    while i < a.Length {
        a[i] := queue.min();
        queue.deleteMin();
        i := i + 1;
    }
}*/
