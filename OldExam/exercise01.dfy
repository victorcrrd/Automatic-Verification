// Final Exam, June 10th, 2021
// We want to specify and verify a method that, given an array of distinct
// elements, computes the number of elements that have a smaller element on
// their right. Example: given the array elements [2,6,8,4,9,5,10], the method
// must return 3 because elements 9, 8 and 6 have smaller elements on their
// right.

// Your tasks are:

// 1. Define a predicate oneBiggerOnRight that given an array v and a valid
// index i on that array, determines if there exists an element on i's right
// that is smaller than v[i]

predicate oneBiggerOnRight(v:array<int>, i:int)
reads v
requires 0 <= i < v.Length {
    exists j :: i < j < v.Length && v[i] > v[j]
}

// 2. Define a function countBiggerOnRight that given an array v and a valid
// index i on that array, returns the number of elements in segment
// [i..v.Length] that meet the property oneBiggerOnRight previously defined

function countBiggerOnRight(v:array<int>, i:int) : (count:int)
reads v
requires 0 <= i < v.Length
decreases v.Length - i {
    if i == v.Length - 1 then 0
    else countBiggerOnRight(v, i+1) + (if oneBiggerOnRight(v, i) then 1 else 0)
}

// 3. Using function countBiggerOnRight, specify a method that receives an array
// v of distinct elements and returns the number of elements that have a smaller
// element on the right

// 4. Implement and verify an algorithm that solves this problem. A linear time
// algorithm will be better valued

method mcountBiggerOnRight(v:array<int>) returns (count:int)
requires v.Length > 0
ensures count == countBiggerOnRight(v, 0) {
    count := 0;
    var i:int := v.Length - 1;
    var min:int := v[i];
    while i > 0
    decreases i
    invariant 0 <= i < v.Length
    invariant forall j :: i <= j < v.Length ==> min <= v[j]
    invariant exists j :: i <= j < v.Length && min == v[j]
    invariant count == countBiggerOnRight(v, i) {
        if v[i-1] > min {
            count := count + 1;
        } else {
            min := v[i-1];
        }
        i := i - 1;
    }
}
