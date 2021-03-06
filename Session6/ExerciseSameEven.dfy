include "ExerciseCountEven.dfy"

method sameEven(v:array<int>) returns (b:bool)
requires positive(v[..])
ensures b <==> countEven(v[..]) == v.Length - countEven(v[..]) {
    ArrayFacts<int>();
    var n:int := mcountEven(v);
    b := n == v.Length - n;
}

method sameEvenB(v:array<int>) returns (b:bool)
requires positive(v[..])
ensures b <==> countEven(v[..]) == v.Length - countEven(v[..]) {
    ArrayFacts<int>();
    var i:int := 0;
    var dif:int := 0;
    while i < v.Length
    decreases v.Length - i
    invariant i <= v.Length
    invariant dif == 2*countEven(v[..i]) - i {
        if v[i] % 2 == 0 {
            assert dif == 2*countEven(v[..i]) - i;
            dif := dif + 1;
            assert dif == 2*countEven(v[..i]) - i + 1;
            assert isEven(v[i]);
            assert countEven(v[..i+1]) == countEven(v[..i]) + 1;
            assert dif == 2*(countEven(v[..i+1]) - 1) - i + 1;
            assert dif == 2*countEven(v[..i+1]) - i - 1;
        } else {
            assert dif == 2*countEven(v[..i]) - i;
            dif := dif - 1;
            assert dif == 2*countEven(v[..i]) - i - 1;
            assert !isEven(v[i]);
            assert countEven(v[..i+1]) == countEven(v[..i]);
            assert dif == 2*countEven(v[..i+1]) - i - 1;
        }
        assert dif == 2*countEven(v[..i+1]) - i - 1;
        i := i + 1;
    }
    b := dif == 0;
}
