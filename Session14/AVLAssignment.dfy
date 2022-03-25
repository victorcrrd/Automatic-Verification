datatype AVL = Empty | Node(left:AVL, height:nat, key:int, right:AVL)

function method empty() : AVL {
    Empty
}

function method node(l:AVL, x:int, r:AVL) : AVL {
    Node(l, 1 + max(myHeight(l), myHeight(r)), x, r)
}

predicate isAVL(t:AVL) {
    match t
        case Empty => true
        case Node(l, h, x, r) => h == height(t) && isAVL(l) && isAVL(r) &&
                                 promising(l, x, r) && -1 <= height(l) - height(r) <= 1
}

function tset(t:AVL) : set<int> {
    match t
        case Empty => {}
        case Node(l, _, x, r) => tset(l) + {x} + tset(r)
}

predicate promising(l:AVL, x:int, r:AVL) {
    (forall z :: z in tset(l) ==> z < x) &&
    (forall z :: z in tset(r) ==> x < z)
}

function method max(x:int, y:int) : int {
    if x >= y then x else y
}

function method abs(x:int) : nat {
    if x < 0 then -x else x
}

function height(t:AVL) : nat {
    match t
        case Empty => 0
        case Node(l, _, _, r) => 1 + max(height(l), height(r))
}

function inorder(t:AVL) : seq<int> {
    match t
        case Empty => []
        case Node(l, _, x, r) => inorder(l) + [x] + inorder(r)
}

function method myHeight(t:AVL) : nat {
    match t
        case Empty => 0
        case Node(_, h, _, _) => h
}

lemma heights(t:AVL)
requires isAVL(t)				
ensures height(t) == myHeight(t) {}

function method search(x:int, t:AVL) : (res:bool)
requires isAVL(t)
ensures res == (x in tset(t)) {
    match t
        case Empty => false
        case Node(l, _, y, r) => if x > y then search(x, r)
                                 else if x < y then search(x, l)
                                 else true
}

function method equil(l:AVL, x:int, r:AVL) : (res:AVL)
requires promising(l, x, r)
requires isAVL(l)
requires isAVL(r)
requires -2 <= height(l) - height(r) <= 2
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset(r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1 {
    if -1 <= myHeight(l) - myHeight(r) <= 1 then node(l, x, r)
    else if myHeight(l) == myHeight(r) + 2 then leftUnbalance(l, x, r)
    else rightUnbalance(l, x, r)
}

function method leftUnbalance(l:AVL, x:int, r:AVL) : (res:AVL)
requires height(l) == height(r) + 2
requires promising(l, x, r)
requires isAVL(l)
requires isAVL(r)
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset (r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1

function method rightUnbalance(l:AVL, x:int, r:AVL) : (res:AVL)
requires height(r) == height(l) + 2
requires promising(l, x, r)
requires isAVL(l)
requires isAVL(r)
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset (r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1

function method insert(x:int, t:AVL) : (res:AVL)
requires isAVL(t)
ensures isAVL(res)
ensures tset(res) == tset(t) + {x}
ensures 0 <= height(res) - height(t) <= 1 {
    match t
        case Empty => node(Empty, x, Empty)
        case Node(l, _, y, r) => if x > y then equil(l, y, insert(x, r))
                                 else if x < y then equil(insert(x, l), y, r)
                                 else t
}

function method delete(x:int, t:AVL) : (res:AVL)
requires isAVL(t)
ensures isAVL(res)
ensures 0 <= height(t) - height(res) <= 1
ensures tset(res) == tset(t) - {x} {
    match t
        case Empty => Empty
        case Node(l, _, y, r) => if x > y then equil(l, y, delete(x, r))
                                 else if x < y then equil(delete(x, l), y, r)
                                 else match r
                                     case Empty => l
                                     case Node(_, _, _, _) => var (m, rp) := deleteMin(r); equil(l, m, rp)
}

function method deleteMin(t:AVL) : (res:(int, AVL))
requires t != Empty
requires isAVL(t)
ensures res.0 in tset(t)
ensures forall z | z in tset(t) :: res.0 <= z
ensures isAVL(res.1)
ensures 0 <= height(t) - height(res.1) <= 1
ensures tset(res.1) == tset(t) - {res.0} {
    match t
        case Node(Empty, _, x, r) => (x, r)
        case Node(l, _, x, r) => var (m, lp) := deleteMin(l);
                                 (m, equil(lp, x, r))
}
