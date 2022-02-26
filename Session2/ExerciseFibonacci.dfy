function fib(n:nat):nat
decreases n {
   if n == 0 then 0
   else if n == 1 then 1
   else fib(n-1) + fib(n-2)
}

method fibonacci1(n:nat) returns (f:nat)
ensures f == fib(n) {
   var i:int := 0;
   f := 0;
   var nextf:int := 1;
   while i < n
   decreases  n - i
   invariant i <= n && f == fib(i) && nextf == fib(i+1) {
      f, nextf := nextf, f + nextf;
      i := i + 1;
   }
}

method fibonacci2(n:nat) returns (f:nat)
ensures f == fib(n) {
   if n == 0 {
      f := 0;
   } else {
      var i:int := 1;
      f := 1;
      var prevf:int := 0;
      while i < n
      decreases n - i
      invariant i <= n && f == fib(i) && prevf == fib(i-1) {
         prevf, f := f, prevf + f;
         i := i + 1;
      }
   }
}

method fibonacci3(n:nat) returns (f:nat)
ensures f == fib(n) {
   var i:int := 0;
   f := 0;
   var a:int := 1;
   while i < n
   decreases n - i
   invariant i <= n && f == fib(i) && (i == 0 ==> a == 1) && (i >= 1 ==> a == fib(i-1)) {
      a, f := f, a + f;
      i := i + 1;
   }
}
