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