datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate sorted(l:List<int>) {
    match l
        case Nil => true
        case Cons(x, Nil) => true
        case Cons(x, Cons(y, xs)) => x <= y && sorted(Cons(y, xs))
}

function elems<T> (l:List<T>) : multiset<T> {
    match l
        case Nil => multiset{}
        case Cons(x, xs) => multiset{x} + elems(xs)
}

lemma sortedSmallList(l:List<int>)
requires length(l) < 2
ensures sorted(l) {}

lemma splitLengths(l:List<int>)
requires length(l) >= 2
ensures length(split(l).0) < length(l)
ensures length(split(l).1) < length(l) {}

method mergesort(l:List<int>) returns (res:List<int>)
decreases length(l)
ensures sorted(res)
ensures elems(l) == elems(res) {
    if length(l) < 2 {
        sortedSmallList(l);
        res := l;
    } else {
        var (left, right) := split(l);
        var resl := mergesort(left);
        var resr := mergesort(right);
        res := merge(resl, resr);
    }
}

function method length<T> (l:List<T>) : nat {
    match l
        case Nil => 0
        case Cons(_, xs) => 1 + length(xs)
}

function method split<T> (l:List<T>) : (res:(List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(l) >= 2 ==> (length(res.0) < length(l) && length(res.1) < length(l)) {
    match l
        case Nil => (Nil, Nil)
        case Cons(x, xs) => var (l1, l2) := split(xs);
                            if length(l1) >= length(l2) then (l1, Cons(x, l2))
                            else (Cons(x, l1), l2)
}

function method merge(l1:List<int>, l2:List<int>) : (res:List<int>)
requires sorted(l1) && sorted(l2)
ensures sorted (res)
ensures elems(res) == elems(l1) + elems(l2) {
    match l1
        case Nil => l2
        case Cons(x, xs) =>
            match l2
                case Nil => l1
                case Cons(y, ys) => if x <= y then Cons(x, merge(xs, l2))
                                    else Cons(y, merge(l1, ys))
}

function partition (l:List<int>, x:int) : (res:(List<int>, List<int>))
ensures forall z | z in elems(res.0) :: z <= x
ensures forall z | z in elems(res.1) :: z > x
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(res.0) <= length(l)
ensures length(res.1) <= length(l) {
    match l
        case Nil => (Nil, Nil)
        case Cons(y, ys) => var (rl, rr) := partition(ys, x);
                            if y <= x then (Cons(y, rl), rr)
                            else (rl, Cons(y, rr))
}

lemma sortedHead(x:int, l:List<int>)
requires sorted(l)
requires forall z | z in elems(l) :: x <= z
ensures sorted(Cons(x, l)) {
    match l
        case Nil => assert sorted(Cons(x, Nil));
        case Cons(y, ys) => assert y in elems(l);
                            assert x <= y;
                            assert sorted(l);
}

// 2. Complete the verification of quicksort.
function quicksort(l:List<int>) : (res:List<int>)
decreases length(l)
ensures sorted(res)
ensures elems(l) == elems(res) {
    match l
        case Nil => Nil
        case Cons(x, xs) => var (l1, l2) := partition(xs, x);
                            var left:List<int> := quicksort(l1);
                            assert sorted(left);
                            var right := quicksort(l2);
                            assert sorted(right);
                            assert forall z | z in elems(left) :: z <= x;
                            assert forall z | z in elems(right) :: x < z;
                            sortedHead(x, right);
                            assert sorted(Cons(x, right));
                            sortedConcat(left, Cons(x, right));
                            assert sorted(concat(left, Cons(x, right)));
                            concat(left, Cons(x, right))
}

function method concat(l1:List<int>, l2:List<int>) : (res:List<int>)
ensures elems(res) == elems(l1) + elems(l2) {
    match l1
        case Nil => l2
        case Cons(x, xs) => Cons(x, concat(xs, l2))
}

lemma sortedConcat(l1:List<int>, l2:List<int>)
requires sorted(l1)
requires sorted(l2)
requires forall z1, z2 | z1 in elems(l1) && z2 in elems(l2) :: z1 <= z2
decreases l1
ensures sorted(concat(l1, l2)) {
    match l1
        case Nil => assert concat(l1, l2) == l2;
                    assert sorted(concat(l1, l2));
        case Cons(x, xs) => headSorted(l1);
                            assert forall z | z in elems(xs) :: x <= z;
                            assert x in elems(l1);
                            assert forall z | z in elems(l2) :: x <= z;
                            assert elems(l1) - multiset{x} == elems(xs);
                            sortedConcat(xs, l2);
                            var conc := concat(xs, l2);
                            assert sorted(conc);
                            assert forall z | z in elems(conc) :: x <= z;
                            assert Cons(x, concat(xs, l2)) == concat(l1, l2);
                            sortedHead(x, conc);
}

function min(x:nat, y:nat) : nat {
    if x <= y then x else y
}

// 1. Modify and verify mergesort using function splitAt n/2 instead of split
function method splitAt<T> (n:nat, l:List<T>) : (res:(List<T>, List<T>))
ensures length(res.0) == min(n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1) {
    if n == 0 then (Nil, l)
    else match l
        case Nil => (Nil, Nil)
        case Cons(x, xs) => var (l1, l2) := splitAt(n-1, xs); (Cons(x, l1), l2)
}

method mergesortModified(l:List<int>) returns (res:List<int>)
decreases length(l)
ensures sorted(res)
ensures elems(l) == elems(res) {
    if length(l) < 2 {
        sortedSmallList(l);
        res := l;
    } else {
        var (left, right) := splitAt(length(l)/2, l);
        var resl := mergesortModified(left);
        var resr := mergesortModified(right);
        res := merge(resl, resr);
    }
}

// 3. Prove the following lemma
lemma uniqueSortedList(l1:List<int>, l2:List<int>)
requires sorted(l1)
requires sorted(l2)
requires elems(l1) == elems(l2)
decreases l1, l2
ensures l1 == l2 {
    match (l1, l2)
        case (Nil, Nil) =>
        case (Cons(x, xs), Nil) =>
        case (Nil, Cons(y, ys)) =>
        case (Cons(x, xs), Cons(y, ys)) => sameHead(l1, l2);
                                           removeFromEqualMultisets(elems(l1), elems(l2), x);
                                           assert elems(l1) - multiset{x} == elems(xs);
                                           assert elems(l2) - multiset{y} == elems(ys);
                                           uniqueSortedList(xs, ys);
}

lemma headSorted(l:List<int>)
requires l != Nil
requires sorted(l)
ensures forall z | z in elems(l.tail) :: l.head <= z {}

lemma sameHead(l1:List<int>, l2:List<int>)
requires l1 != Nil
requires sorted(l1)
requires l2 != Nil
requires sorted(l2)
requires elems(l1) == elems(l2)
ensures l1.head == l2.head {
    headSorted(l2);
    assert forall z | z in elems(l2) :: l2.head <= z;
    assert forall z | z in elems(l1) :: l2.head <= z;
    assert l1.head in elems(l1);
    assert l2.head <= l1.head;
    headSorted(l1);
    assert forall z | z in elems(l2) :: l1.head <= z;
    assert l2.head in elems(l2);
    assert l1.head <= l2.head;
}

lemma removeFromEqualMultisets(m1:multiset<int>, m2:multiset<int>, x:int)
requires x in m1
requires x in m2
requires m1 == m2
ensures m1 - multiset{x} == m2 - multiset{x} {}
