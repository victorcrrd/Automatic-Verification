include "ExerciseSumElems.dfy"

function sumM(m:multiset<int>):int
decreases m {
    if m == multiset{} then 0
    else var x :| x in m; x + sumM(m - multiset{x})
}

function sumSM(s:seq<int>):int {
    sumM(multiset(s))
}

function sumVM(v:array<int>, c:int, f:int):int
requires 0 <= c <= f <= v.Length
reads v {
    sumSM(v[c..f])
}

lemma {:induction m} sumOne(m:multiset<int>, x:int)
decreases m
requires x in m
ensures sumM(m) == x + sumM(m - multiset{x}) {
    var y :| y in m && sumM(m) == y + sumM(m - multiset{y});
    if x == y {
        return;
    } else {
        calc == {
            sumM(m);
            y + sumM(m - multiset{y});
            { sumOne(m - multiset{y}, x); }
            y + x + sumM(m - multiset{y} - multiset{x});
            { assert m - multiset{x} - multiset{y} == m - multiset{y} - multiset{x}; }
            x + y + sumM(m - multiset{x} - multiset{y});
			{ sumOne(m - multiset{x}, y); }
			x + sumM(m - multiset{x});
        }
    }
}

lemma {:induction m, n} sumByParts(m:multiset<int>, n:multiset<int>)
decreases m, n
ensures sumM(m + n) == sumM(m) + sumM(n) {
    if m == multiset{} {
        assert m + n == n;
    } else if n == multiset{} {
        assert m + n == m;
    } else {
        var x :| x in m;
        sumByParts(m - multiset{x}, n);
        assert (m - multiset{x}) + n == (m + n) - multiset{x};
        assert sumM((m - multiset{x}) + n) == sumM((m + n) - multiset{x});
        sumOne(m, x);
        sumOne(m + n, x);
    }
}

lemma {:induction s} sumS(s:seq<int>)
decreases s
ensures sumSM(s) == sumL(s)
ensures sumSM(s) == sumR(s) {
    equalSum(s, 0, |s|);
    if s != [] {
        SeqFacts<int>();
        assert multiset(s[0..|s|]) == multiset(s[0..|s|-1]) + multiset(s[|s|-1..|s|]);
        assert multiset{s[|s|-1]} == multiset(s[|s|-1..|s|]);
        calc == {
            sumSM(s);
            { sumOne(multiset(s[0..|s|]), s[|s|-1]); }
            sumSM(s[..|s|-1]) + s[|s|-1];
            //sumR(s);
            //sumR(s[..|s|-1]) + s[|s|-1];
            //{ sumS(s[..|s|-1]); }
            //sumSM(s[..|s|-1]) + s[|s|-1];
            //{ sumOne(multiset(s[..|s|-1]), s[|s|-1]); }
            //sumSM(s);
        }
    }
}

lemma SeqFacts<T>()
    ensures forall s:seq<T> | |s| >= 1 :: |s[1..|s|]| == |s|-1;
    ensures forall s:seq<T>, i, j | 0 <= i <= j <= |s| :: |s[i..j]| == j-i
    ensures forall s:seq<T>, i, j | 0 <= i < j <= |s| :: s[i..j][..(j-i)-1] == s[i..j-1]
    ensures forall s:seq<T>, i, j, k | 0 <= i <= k <= j <= |s| :: multiset(s[i..k]) + multiset(s[k..j]) == multiset(s[i..j]) {
        forall s : seq<T>, i, j, k | 0 <= i <= k <= j <= |s|
        ensures multiset(s[i..k]) + multiset(s[k..j]) == multiset(s[i..j]) {
            assert s[i..k] + s[k..j] == s[i..j];
        }
    }

/*
//Prove this using SumOne


lemma  decomposeM(v:array<int>,c:int,f:int)
requires 0<=c<f<=v.Length
ensures SumVM(v,c,f)==SumVM(v,c,f-1)+v[f-1]
ensures SumVM(v,c,f)==v[c]+SumVM(v,c+1,f)
//Prove this using SumByParts

lemma {:induction s,r} sumElemsS(s:seq<int>,r:seq<int>)
requires multiset(s)==multiset(r)
//ensures SumR(s)==SumR(r)
//ensures SumL(s)==SumL(r)
ensures SumS(s)==SumS(r)
{}





lemma ArrayFactsM<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
    ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
    ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
  ensures forall v:array<int>,i,j | 0<=i<j<=v.Length::SumVM(v,i,j)==SumVM(v,i,j-1)+v[j-1]
  ensures forall v:array<int>,i,j | 0<=i<j<=v.Length::SumVM(v,i,j)==v[i]+SumVM(v,i+1,j) 
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length ::SumS(v[i..j])==SumR(v[i..j])
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length ::SumS(v[i..j])==SumL(v[i..j])
  ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length ::SumV(v,i,j)==SumVM(v,i,j)==SumL(v[i..j])==SumR(v[i..j])==SumS(v[i..j])
  ensures forall v:array<int>,i,j,k | 0<=i<=k<=j<=v.Length ::SumVM(v,i,j)==SumVM(v,i,k)+SumVM(v,k,j)
{equalSumsV();
SeqFacts<int>();

  forall v:array<int>,i,j | 0<=i<j<=v.Length
  ensures SumVM(v,i,j)==SumVM(v,i,j-1)+v[j-1]
  {decomposeM(v,i,j);}

  forall v:array<int>,i,j | 0<=i<j<=v.Length
   ensures SumVM(v,i,j)==v[i]+SumVM(v,i+1,j) 
   {decomposeM(v,i,j);}

   forall s:seq<int>
   ensures SumS(s)==SumR(s)
   ensures SumS(s)==SumL(s)
   {sums(s);}

   //Prove the last property

}





  method sumElems3(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
//ensures sum==SumR(v[..])
ensures sum==SumVM(v,0,v.Length)

{ArrayFactsM<int>();
 sum:=0;
 var i:int;
 i:=0; var m:=v.Length/2;
 while (i<m) //First loop computes the sum [0..m)
   decreases //Write 
   invariant //write
 {
  sum:=sum+v[i];
  i:=i+1;
  }
  assert sum==SumVM(v,0,m);
  var aux:=0;
  assert i==m;
  while (i<v.Length)
   decreases //write
   invariant //write
  {
    aux:=aux+v[i];
    i:=i+1;
  }
  assert aux==SumVM(v,m,v.Length);
    sum:=sum+aux;
}*/


