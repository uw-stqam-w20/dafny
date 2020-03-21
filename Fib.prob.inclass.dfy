/**
   This is an in-class version of the problem.
   See Fib.prob.dfy for complete problem description.
 */
/*
  fib(0) == 0     fib(1) == 1            fib(i) == fib(i-1) + fib(i-2)
*/
function fib (n: nat) : nat
{
  // YOUR CODE HERE
}


method Fib (n: nat) returns (b: nat)
  // YOUR SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}





















/*
method Fib (n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if (n == 0) { return 0; }
  var a := 0;
  b := 1;

  var i := 1;
  while (i < n)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
*/
