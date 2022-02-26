method mroot1(n:int) returns (r:int) // O(sqrt n)
requires n >= 0
ensures r >= 0 && r*r <= n < (r+1)*(r+1) {
	r := 0;
	while (r+1)*(r+1) <= n
	decreases n - r*r
	invariant r >= 0 && r*r <= n {
		r := r + 1;
	}
}

method mroot2(n:int) returns (r:int) // O(n)
requires n >= 0
ensures r >= 0 && r*r <= n < (r+1)*(r+1) {
	r := n;
	while n < r*r
	decreases r 
	invariant 0 <= r && n < (r+1)*(r+1) {
		r := r - 1;
	}
}

method mroot3(n:int) returns (r:int) // O(log n)
requires n >= 0
ensures r >= 0 && r*r <= n < (r+1)*(r+1) {
	var y:int := n+1;
	var h:int;
	r := 0;
	// Search in interval [r, y)
	while y != r + 1
	decreases y - r
	invariant 0 <= r < y <= n+1 && r*r <= n < y*y {
		h := (r + y) / 2;
		if h*h <= n {
			r := h;
		} else {
			y := h;
		}
	}
}
