// Method barrier below receives an array and an integer p
// and returns a boolean b which is true if and only if
// all the positions to the left of p and including also position p contain elements
// that are strictly smaller than all the elements contained in the positions to the right of p
// Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false,
// but for p=2 the method should return true
// 1.Specify the method
// 2.Implement an O(v.size()) method
// 3.Verify the method

method barrier(v:array<int>, p:int) returns (b:bool)
requires 0 <= p < v.Length
ensures b == (forall k, h :: 0 <= k <= p < h < v.Length ==> v[k] < v[h]) {
    var max:int := v[0];
    var i:int := 1;
    while i <= p
    decreases p - i
    invariant i <= p + 1
    invariant forall k :: 0 <= k < i ==> max >= v[k]
    invariant exists kp :: 0 <= kp < i && max == v[kp] {
        if v[i] > max {
            max := v[i];
        }
        i := i + 1;
    }

    assert i == p + 1;
    assert forall k :: 0 <= k <= p ==> max >= v[k];
    
    b := true;
    while i < v.Length && b
    decreases v.Length - i
    invariant i <= v.Length
    invariant b == (forall h :: p < h < i ==> v[h] > max) {
        if max >= v[i] {
            b := false;
        }
        i := i + 1;
    }
    assert b == (forall k, h :: 0 <= k <= p < h < v.Length ==> v[h] > max >= v[k]);
}
