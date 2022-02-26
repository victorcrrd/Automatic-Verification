predicate strictSorted(s:seq<int>) {
	forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

method mcontained(v:array<int>, w:array<int>, n:int, m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
