datatype List<T> = Nil | Cons(head:T, tail:List<T>)

function method length<T> (l:List<T>) : nat
ensures l.Nil? <==> length(l) == 0 {
    match l
        case Nil => 0
        case Cons(_, xs) => 1 + length(xs)
}

predicate sorted(l:List<int>) {
    match l
        case Nil => true
        case Cons(x, Nil) => true
        case Cons(x, Cons(y, ys)) => x <= y && sorted(Cons(y, ys))
}

function elems<T> (l:List<T>) : multiset<T> {
    match l
        case Nil => multiset{}
        case Cons(x, xs) => multiset{x} + elems(xs)
}

function min(x:nat, y:nat) : nat {
    if x <= y then x else y
}

function insert(x:int, l:List<int>) : (res:List<int>)
requires sorted(l)
ensures sorted(res)
ensures elems(res) == multiset{x} + elems(l) {
    match l
        case Nil => Cons(x, Nil)
        case Cons(y, ys) => if x <= y then Cons(x, Cons(y, ys))
                            else Cons(y, insert(x, ys))
}

function delete<T> (x:T, l:List<T>) : (res:List<T>)
ensures elems(res) == elems(l) - multiset{x} {
    match l
        case Nil => Nil
        case Cons(y, ys) => if x == y then ys
                            else Cons(y, delete(x, ys))
}

function search<T> (x:T, l:List<T>) : (res:bool)
ensures res == (x in elems(l)) {
    match l
        case Nil => false
        case Cons(y, ys) => if x == y then true
                            else search(x, ys)
}

function take<T> (n:nat, l:List<T>) : (res:List<T>)
ensures length(res) == min(n, length(l)) {
    if n == 0 then Nil else match l
        case Nil => Nil
        case Cons(x, xs) => Cons(x, take(n-1, xs))
}

function drop<T> (n:nat, l:List<T>) : (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n {
    if n == 0 then l else match l
        case Nil => Nil
        case Cons(x, xs) => drop(n-1, xs)
}

// 1. Write the code of the split function and verify it
function method split<T> (n:nat, l:List<T>) : (res:(List<T>, List<T>))
ensures length(res.0) == min(n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1) {
    if n == 0 then (Nil, l)
    else match l
        case Nil => (Nil, Nil)
        case Cons(x, xs) => var (l1, l2) := split(n-1, xs); (Cons(x, l1), l2)
}

// 2. Specify, write the code of the following function and verify it.
function method reverse<T> (l:List<T>) : (res:List<T>)
ensures length(res) == length(l)
ensures elems(res) == elems(l)
ensures l.Nil? ==> res == l
ensures l.Cons? ==> res == concat(reverse(l.tail), Cons(l.head, Nil)) {
    match l
        case Nil => Nil
        case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil))
}

// 3. Specify, write the code of the following function and verify it.
function method concat<T> (l1:List<T>, l2:List<T>) : (res:List<T>)
ensures length(res) == length(l1) + length(l2)
ensures elems(res) == elems(l1) + elems(l2)
ensures split(length(l1), res) == (l1, l2) {
    match l1
        case Nil => l2
        case Cons(x, xs) => Cons(x, concat(xs, l2))
}

// 4. Prove the following lemma.
lemma concatAssoc<T> (l1:List<T>, l2:List<T>, l3:List<T>)
ensures concat(l1, concat(l2, l3)) == concat(concat(l1, l2), l3) {}

// 5. Prove the following lemma.
lemma reverseIdemp<T> (l:List<T>)
decreases l
ensures reverse(reverse(l)) == l {
    if l.Cons? {
        calc == {
            reverse(reverse(l));
            reverse(concat(reverse(l.tail), Cons(l.head, Nil)));
            { reverseConcat(l.head, reverse(l.tail)); }
            Cons(l.head, reverse(reverse(l.tail)));
            { reverseIdemp(l.tail); }
            Cons(l.head, l.tail);
            l;
        }
    }
}

// Auxiliary lemma.
lemma reverseConcat<T>(head:T, tail:List<T>)
ensures reverse(concat(tail, Cons(head, Nil))) == Cons(head, reverse(tail)) {}
