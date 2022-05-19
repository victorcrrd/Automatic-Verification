// Final Exam, June 10th, 2021
// Exercise on algebraic datatypes [4pts]
// You are given the definitions below and you are asked to represent sets of
// integers as sorted lists of integers without duplicates. You are also given
// the specifications of the emptySet, singleton, union and intersection
// functions. Your task consists of implementing and verifying them. The cost of
// union and intersection should in O(n1+n2), being n1 and n2 the cardinals of
// the sets received as arguments. 

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate noDup <T> (l:List<T>) {
    match l
        case Nil => true
        case Cons(x, xs) => x !in elems(xs) && noDup(xs)
}

predicate sorted(l:List<int>) {
    match l 
       case Nil => true
       case Cons(x, xs) => 
            match xs 
               case Nil => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems <T> (l:List<T>) : set<T> {
    match l
       case Nil => {}
       case Cons(x, xs) => {x} + elems(xs)
}

// [0.1pts]
function method emptySet() : (res:List<int>)
ensures elems(res) == {} {
    Nil
}

// [0.1pts]
function method singleton(x:int) : (res:List<int>)
ensures elems(res) == {x} && noDup(res) {
    Cons(x, Nil)
}

predicate strictlySorted (l:List<int>) {
    match l 
       case Nil => true
       case Cons(x, xs) => 
            match xs 
               case Nil => true
               case Cons(y, ys) => x < y && strictlySorted(xs)
}

lemma sortedAndNotDuplicatedMeansStrictlySorted(l:List<int>)
requires sorted(l)
requires noDup(l)
ensures strictlySorted(l) {}

lemma headSmallerThanTail(l:List<int>)
requires l.Cons?
requires strictlySorted(l)
ensures forall x :: x in elems(l.tail) ==> l.head < x {}

// [1.8pts]
function method union(l1:List<int>, l2:List<int>) : (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res)
ensures noDup(res)
ensures elems(res) == elems(l1) + elems (l2) {
    sortedAndNotDuplicatedMeansStrictlySorted(l1);
    sortedAndNotDuplicatedMeansStrictlySorted(l2);
    match l1
        case Nil => l2
        case Cons(x, xs) =>
            match l2
                case Nil => l1
                case Cons(y, ys) => headSmallerThanTail(l1);
                                    headSmallerThanTail(l2);
                                    if x < y then
                                    Cons(x, union(xs, l2))
                                    else if x == y then
                                    Cons(x, union(xs, ys))
                                    else
                                    Cons(y, union(l1, ys))
}

// [2pts]
function method inters(l1:List<int>, l2:List<int>) : (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) * elems (l2) {
    sortedAndNotDuplicatedMeansStrictlySorted(l1);
    sortedAndNotDuplicatedMeansStrictlySorted(l2);
    match l1
        case Nil => emptySet()
        case Cons(x, xs) =>
            match l2
            case Nil => emptySet()
            case Cons(y, ys) => headSmallerThanTail(l1);
                                headSmallerThanTail(l2);
                                if x < y then
                                inters(xs, l2)
                                else if x == y then
                                Cons(x, inters(xs, ys))
                                else
                                inters(l1, ys)
}
