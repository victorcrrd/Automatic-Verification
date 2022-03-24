datatype Skew = Empty | Node(left:Skew, key:int, right:Skew)

predicate isSkew(t:Skew) {
    match t
        case Empty => true
        case Node(l, x, r) => heap(l, x, r) && isSkew(l) && isSkew(r)
}

function mset(t:Skew) : multiset<int> {
    match t
        case Empty => multiset{}
        case Node(l, x, r) => mset(l) + multiset{x} + mset(r)
}

predicate heap(l:Skew, x:int, r:Skew) {
    forall z | z in mset(l) + mset(r) :: x <= z
}

// 1. Provide the specification and verification of the following join function method.
function method join(t1:Skew, t2:Skew) : (res:Skew)
requires isSkew(t1)
requires isSkew(t2)
decreases t1, t2
ensures isSkew(res)
ensures mset(res) == mset(t1) + mset(t2) {
    match t1
        case Empty => t2
        case Node(l1, x1, r1) => match t2
            case Empty => t1
            case Node(l2, x2, r2) =>
                if x1 <= x2 then
                    assert isSkew(join(r1, t2));
                    assert isSkew(l1);

                    assert forall z | z in mset(l2) + mset(r2) :: x1 <= x2 <= z;
                    subsetAndElemIneq(x1, mset(l2) + mset(r2), x2);
                    assert forall z | z in mset(l2) + mset(r2) + multiset{x2} :: x1 <= z;
                    assert mset(t2) == mset(l2) + mset(r2) + multiset{x2};
                    assert forall z | z in mset(t2) :: x1 <= z;
                    assert mset(r1) <= mset(l1) + mset(r1);
                    assert forall z | z in mset(r1) :: x1 <= z;
                    assert forall z | z in mset(r1) + mset(t2) :: x1 <= z;

                    assert mset(l1) <= mset(l1) + mset(r1);
                    assert forall z | z in mset(l1) :: x1 <= z;

                    Node(join(r1, t2), x1, l1)
                else
                    assert isSkew(join(t1, r2));
                    assert isSkew(l2);

                    assert forall z | z in mset(l1) + mset(r1) :: x2 < x1 <= z;
                    subsetAndElemIneq(x2, mset(l1) + mset(r1), x1);
                    assert forall z | z in mset(l1) + mset(r1) + multiset{x1} :: x2 <= z;
                    assert mset(t1) == mset(l1) + mset(r1) + multiset{x1};
                    assert forall z | z in mset(t1) :: x2 <= z;
                    assert mset(r2) <= mset(l2) + mset(r2);
                    assert forall z | z in mset(r2) :: x2 <= z;
                    assert forall z | z in mset(r2) + mset(t1) :: x2 <= z;

                    assert mset(l2) <= mset(l2) + mset(r2);
                    assert forall z | z in mset(l2) :: x2 <= z;

                    Node(join(t1, r2), x2, l2)
}

lemma subsetAndElemIneq(x:int, m:multiset<int>, elem:int)
requires x <= elem
requires forall z | z in m :: x <= z
ensures forall z | z in m + multiset{elem} :: x <= z {}

// 2. Provide the specification, code and verification of the following function method.
function method insert(x:int, t:Skew) : (res:Skew)
requires isSkew(t)
ensures isSkew(res)
ensures mset(res) == mset(t) + multiset{x} {
    join(Node(Empty, x, Empty), t)
}

// 3. Provide the specification, code and verification of the following function method.
function method min(t:Skew) : (res:int)
requires t.Node?
requires isSkew(t)
ensures forall z | z in mset(t) :: res <= z {
    assert mset(t) == mset(t.left) + mset(t.right) + multiset{t.key};
    subsetAndElemIneq(t.key, mset(t.left) + mset(t.right), t.key);
    t.key
}

// 4. Provide the specification, code and verification of the following function method.
function method deleteMin(t:Skew) : (res:Skew)
requires t.Node?
requires isSkew(t)
ensures isSkew(res)
ensures mset(res) == mset(t) - multiset{min(t)} {
    join(t.left, t.right)
}
