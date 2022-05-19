/*
    Final Exam, May 19th, 2022
    Exercise on algebraic datatypes: 4 points

    You are given the definitions below and you are asked to represent
    sets of integers as sorted lists of integers without duplicates

    You are also given the specifications of the emptySet, singleton, union and 
    intersection functions. Your task consists of implementing and verifying 
    them. The cost of union and intersection should in O(n1+n2), being n1 and n2
    the cardinals of the sets received as arguments. 
*/

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate noDup <T> (l:List<T>)
{
    match l
        case Nil        => true
        case Cons(x,xs) => x !in elems(xs) && noDup(xs)
}

predicate sorted (l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems <T> (l:List<T>) : set<T>
{
    match l
       case Nil         => {}
       case Cons(x, xs) => {x} + elems(xs)
}

///////////////////// implement and verify /////////////////////////////////

// 0.1 points

function method emptySet() : (res:List<int>)
ensures elems(res) == {}

// 0.1 points

function method singleton(x:int): (res:List<int>)
ensures elems(res) == {x} && noDup(res)

// 1.8 points

function method union (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) + elems (l2)

// 2 points

function method inters (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) * elems (l2)
