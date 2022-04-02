predicate strictSorted(s:seq<int>) {
	forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

// Specify and implement an O(m+n) algorithm that returns b, where v and w are
// strictly increasing ordered arrays and it's ensured that b is true iff the
// first n elements of v are contained in the first m elements of w
method mcontained(v:array<int>, w:array<int>, n:int, m:int) returns (b:bool)
requires strictSorted(v[..])
requires 0 <= n <= v.Length
requires strictSorted(w[..])
requires 0 <= m <= w.Length
requires n <= m
ensures b == (forall i :: 0 <= i < n ==> (exists j :: 0 <= j < m && v[i] == w[j])) {
	var i:int := 0;
	var j:int := 0;
	b := true;
	while i < n && j < m && b
	decreases n - i, m - j, b
	invariant 0 <= i <= n
	invariant 0 <= j <= m
	invariant b ==> (forall k :: 0 <= k < i ==> (exists l :: 0 <= l < j && v[k] == w[l]))
	{
		if v[i] == w[j] {
			i := i + 1;
			j := j + 1;
		} else if w[j] < v[i] {
			j := j + 1;
		} else {
			b := false;
		}
	}
}