/**
   This is an in-class version of the problem.
   See factorial.prob.dfy for complete problem description.
 */
/*
   (a) 1! = 1
   (b) n! = n*(n-1)! for n > 1
*/
function factorial (n :nat) : nat
  // YOUR SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}

method Factorial (n: nat) returns (v:nat)
  // YOUR SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}



































/*
method Factorial (n: nat) returns (v:nat)
  requires n > 0;
  ensures v == factorial(n);
{
  v := 1;
  if (n == 1) { return v; }
  var i := 2;
  while (i <= n)
  {
    v := i * v;
    i := i + 1;
  }
  return v;
}

*/
