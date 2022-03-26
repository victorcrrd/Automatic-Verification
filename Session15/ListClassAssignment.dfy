class Node {
    var val:int;
    var next:Node?;
    ghost var repr:set<object>; // objects that can be seen from this node
    ghost var model:seq<int>; // sequence of values of the list starting at this node

    predicate Valid()
    reads this, repr
    decreases repr {
        this in repr &&
        (next == null ==> model == [val]) &&
        (next != null ==> next in repr && next.repr <= repr &&
            this !in next.repr && model == [val] + next.model && next.Valid())
    }
    
    constructor(v:int)
    ensures Valid()
    ensures fresh(repr)
    ensures model == [v] {
        val := v;
        next := null;
        repr := {this};
        model := [v];
    }

    function length() : (l:nat)
    reads repr
    requires Valid()
    decreases repr
    ensures l == |model| {
        if next == null then 1 else 1 + next.length()
    }

    method append(node:Node)
}

class List {
    var first:Node?;
    ghost var repr:set<object>;
    ghost var model:seq<int>;

    predicate Valid()
    reads this, repr {
        this in repr &&
        (first == null ==> model == []) &&
        (first != null ==> first in repr && first.repr <= repr &&
            this !in first.repr && first.Valid() && model == first.model)
    }

    constructor()
    ensures Valid()
    ensures fresh(repr)
    ensures model == [] {
        first := null;
        repr := {this};
        model := [];
    }

    function length() : (l:nat)
    reads this, repr
    requires Valid()
    ensures l == |model| {
        if first == null then 0 else first.length()
    }

    method add(v:int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures model == [v] + old(model) {
        var node := new Node(v);
        node.next := first;
        node.repr := node.repr + if first == null then {} else first.repr;
        node.model := node.model + if first == null then [] else first.model;
        first := node;
        repr := {this} + first.repr;
        model := first.model;
    }

    method append(v:int)
}

method main() {
    var l := new List();
    assert l.length() == 0;
    l.add(1);
    assert l.length() == 1;
    l.add(2);
    assert l.length() == 2;
    //l.append(7);
    //assert l.length() == 3;
    //assert l.model == [2, 1, 7];
}
