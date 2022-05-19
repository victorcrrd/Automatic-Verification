
//EXERCISE 1: 6 points
//We want to check if an array w is a "slipped version" of another array v of the same Length
//We say that w is a slipped version of v at index k if v[0]==w[k] and the sequence of elements
//are the same in both arrays considering w as circular v[1]==w[k+1], v[2]==w[k+2]....etc
// As example : given v=[2,5,1,6,8] and w=[6,8,2,5,1], w is a slipped version of v at index 2
// as v[0]==w[2], v[1]==w[3], v[2]==w[4], v[3]==w[0] and v[4]==w[1]
//We will solve the problem for arrays where all the elements are different.

//1. [0.5pt] Define the following predicates 
predicate different(v : array<int>) 
 reads v;
//All the elements in v are different

predicate slipped(v : array<int>,w : array<int>, k:int)
 requires v.Length == w.Length && 0 <= k < v.Length
 reads v,w
 //The elements of v and w are the same starting at index k: 
 //v[0]==w[k] and so on circularly on w
 //Hint: use %


//2.[1.5pts] Prove the following lemmas
 
//2.1 If v[0] is not in w then w is not a slipped version of v for any k
 lemma firstMustAppear(v:array<int>, w:array<int>)
 requires v.Length>=0 && w.Length==v.Length
 requires (forall k:: 0 <= k < v.Length ==> v[0] != w[k]) 
 ensures  (forall k:: 0 <= k < v.Length ==> !slipped(v,w,k))
 
//2.2 If v[0]==w[i] but w is not a slipped version of v at index i
//then there is no other possibility of being a slipped version of v
  
  lemma onlyPossibility(v:array<int>, w:array<int>,i:int)
   requires v.Length>0 && w.Length==v.Length && 0<=i<v.Length && different(v) && different(w) && v[0]==w[i]
   requires !slipped(v,w,i)
   ensures (forall k:: 0 <= k < v.Length ==> !slipped(v,w,k))
   
//3.[1 pts] Write the postcondition of method mslipped
// b is true if and only if w is a slipped version of v
// If b is true then w is a slipped version of v from index i
// If b is false i must b v.Length  

method mslipped(v : array<int>,w : array<int>) returns (b : bool,i:int)
	requires v.Length > 0 && v.Length==w.Length && different(v) && different(w)


//4. [3 pts] Implement and verify the method that given two arrays v and w containing different elements
//checks if w is a slipped version of v
//First write a loop for looking v[0] in w. If it does not appear then w cannot be a slipped version of v.
//Otherwise if v[0]==w[i], write a loop to check circularly the rest of elements
//Use the previous lemmas to verify

