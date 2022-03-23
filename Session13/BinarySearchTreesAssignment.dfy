// BSTs are binary trees having unique keys and sorted inorder traversal
datatype BST = Empty | Node(left:BST, key:int, right:BST)

function tset(t:BST) : set<int> {
    match t
        case Empty => {}
        case Node(l, x, r) => tset(l) + {x} + tset(r)
}

predicate isBST(t:BST) {
    match t
        case Empty => true
        case Node(l, x, r) => promising(l, x, r) && isBST(l) && isBST(r)
}

predicate promising(l:BST, x:int, r:BST) {
    (forall z :: z in tset(l) ==> z < x) &&
    (forall z :: z in tset(r) ==> x < z)
}

// all the elements in one tree are bigger than all the elements in the other
predicate bigger(t1:BST, t2:BST) {
    biggerThan(t1, t2) || biggerThan(t2, t1)
}

// all the elements in t1 are bigger than all the elements in t2
predicate biggerThan(t1:BST, t2:BST) {
    forall x1, x2 :: x1 in tset(t1) && x2 in tset(t2) ==> x1 > x2
}

function inorder(t:BST) : seq<int> {
    match t
        case Empty => []
        case Node(l, x, r) => inorder(l) + [x] + inorder(r)
}

function method search(x:int, t:BST) : (res:bool)
requires isBST(t)
ensures res == (x in tset(t)) {
    match t
        case Empty => false
        case Node(l, y, r) => x == y || search(x, l) || search(x, r)
}

function method insert(x:int, t:BST) : (res:BST)
requires isBST(t)
ensures isBST(res)
ensures tset(res) == {x} + tset(t) {
    match t
        case Empty => Node(Empty, x, Empty)
        case Node(l, y, r) => if x > y then Node(l, y, insert(x, r))
                              else if x < y then Node(insert(x, l), y, r)
                              else t
}

function method delete(x:int, t:BST) : (res:BST)
requires isBST(t)
ensures isBST(res)
ensures tset(res) == tset(t) - {x} {
    match t
        case Empty => Empty
        case Node(l, y, r) =>
            if x > y then Node(l, y, delete(x, r))
            else if x < y then Node(delete(x, l), y, r)
            else union(l, r)
}

function method union(t1:BST, t2:BST) : (res:BST)
requires isBST(t1)
requires isBST(t2)
requires bigger(t1, t2)
ensures isBST(res)
ensures tset(res) == tset(t1) + tset(t2) {
    match (t1, t2)
        case (Empty, Empty) => Empty
        case (Node(_,_,_), Empty) => t1
        case (Empty, Node(_,_,_)) => t2
        case (Node(l1, x1, r1), Node(l2, x2, r2)) =>
            assert x1 in tset(t1) && x2 in tset(t2);
            assert x1 != x2;
            if x1 < x2 then Node(Node(l1, x1, union(r1, l2)), x2, r2)
            else Node(Node(l2, x2, union(l1, r2)), x1, r1)
}

predicate sorted(s:seq<int>) {
    forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

lemma sortedInorder(t:BST)
requires isBST(t)
ensures sorted(inorder(t)) {
    match t
        case Empty =>
        case Node(l, x, r) =>
            assert promising(l, x, r);
            inorderPreserveSet(l);
            assert forall z | z in inorder(l) :: z in tset(l);
            assert forall z | z in inorder(l) :: z < x;
            inorderPreserveSet(r);
            assert forall z | z in inorder(r) :: z > x;
            assert inorder(t)[|inorder(l)|] == x;
            assert forall j | 0 <= j < |inorder(l)| :: inorder(t)[j] in tset(l);
            assert forall j | |inorder(l)| < j < |inorder(t)| :: inorder(t)[j] in tset(r);
}

lemma inorderPreserveSet(t:BST)
ensures forall z :: z in inorder(t) <==> z in tset(t) {}

// 1. Program a function mirror that gets the symmetrix image of a tree along a
// vertical axis passing through the root and prove the given postcondition.
function mirror(t:BST) : (res:BST)
ensures mirrorOf(t, res) {
    match t
        case Empty => Empty
        case Node(l, x, r) => Node(mirror(r), x, mirror(l))
}

// a tree is the mirror of another
predicate mirrorOf(t:BST, s:BST) {
    match (t, s)
        case (Empty, Empty) => true
        case (Empty, Node(_,_,_)) => false
        case (Node(_,_,_), Empty) => false
        case (Node(l1, x1, r1), Node(l2, x2, r2)) => x1 == x2 && mirrorOf(l1, r2) && mirrorOf(r1, l2)
}

lemma mirrorIdempotent(t:BST)
ensures mirror(mirror(t)) == t {}

// 2. Given the following rev function, prove the following lemma:
function rev<T>(s:seq<T>) : (res:seq<T>) {
    if s == [] then []
    else rev(s[1..]) + [s[0]]
}

lemma reverseConcat<T>(s1:seq<T>, s2:seq<T>)
decreases s1 + s2
ensures rev(s1 + s2) == rev(s2) + rev(s1) {
    if s1 == [] {
        assert [] + s2 == s2;
        assert rev([] + s2) == rev(s2) == rev(s2) + [];
    } else if s2 == [] {
        assert s1 + [] == s1;
        assert rev(s1 + []) == rev(s1) == [] + rev(s1);
    } else {
        ghost var s12 := s1 + s2;
        assert s12[1..] == s1[1..] + s2;
        calc == {
            rev(s1 + s2);
            rev([s12[0]] + s12[1..]);
            rev(s12[1..]) + [s12[0]];
            { reverseConcat(s1[1..], s2); }
        }
    }
}

lemma reverseInorder(t:BST)
decreases t
ensures inorder(mirror(t)) == rev(inorder(t)) {
    match t
        case Empty =>
        case Node(l, x, r) => calc == {
            inorder(mirror(t));
            inorder(mirror(Node(l, x, r)));
            inorder(mirror(r)) + [x] + inorder(mirror(l));
            { reverseInorder(l); reverseInorder(r); }
            rev(inorder(r)) + [x] + rev(inorder(l));
            { reverseConcat(inorder(r), [x]); }
            rev([x] + inorder(r)) + rev(inorder(l));
            { reverseConcat(inorder(l), [x] + inorder(r)); }
            rev(inorder(l) + ([x] + inorder(r)));
            { assert inorder(l) + ([x] + inorder(r)) == inorder(l) + [x] + inorder(r); }
            rev(inorder(l) + [x] + inorder(r));
            rev(inorder(Node(l, x, r)));
            rev(inorder(t));
        }
}
