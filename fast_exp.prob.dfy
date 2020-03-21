/*
   Fast exponentiation is an algorithm to compute 'x to the power of y' by
   repeatedly computing x squared until the desired result is achieved.
   https://en.wikipedia.org/wiki/Exponentiation_by_squaring

   The algorithm is based on the following well-known equivalences

   x**0 == 1
   x**1 == x
   x**n == (x*x) * (n/2)    if n is even
   x**n == (x*x) * (n-1/2)  if n is odd

  The goal of this exercise is to specify and verify a function that implements
  exponentiation by repeated squaring

   This involves three steps

   (1) Formally define a (recursive) mathematical function for exponent. The
       function must be well-defined. That is, for each input, it must produce a
       correct output. The function might be not defined for certain inputs (for
       example, not defined for negative numbers), but must formally state the
       domain on which it is defined.

   (2) Implement and specify a method to compute a exponentiation by squaring.
       As a hint, the code of the function is provided to you. However, you
       still need to write the proper specification.

   (3) Complete the verification of the method from part (b). This requires
       providing the necessary inductive invariant for each loop and ranking
       arguments (where necessary) to ensure that each loop terminates and the
       function computes the desired result. Furthermore, this will require
       to help Dafny with reasoning about exponentiation. Three helpful lemmas
       are provided as a hint

   (4) Complete proofs of the provided lemmas by elaborating their bodies.
*/

/***********************************************************************/
/*                            PART 1                                   */
/***********************************************************************/

/**
   Define function exp for computing an exponent of the number. Use the facts that
   exp(x, 0) == 1
   exp(x, 1) == x
   exp(x, n) == x*exp(x, n-1)
   */
function exp(x: real, n:nat) real
  // YOUR SPEC HERE (might be empty)
{
  // YOUR CODE HERE
}

/***********************************************************************/
/*                            LEMMAS                                   */
/* The following lemmas are provided as a hint. Use them in part 3,    */
/*   prove that they are correct in part 4.                            */
/***********************************************************************/


/*
   This lemma states multiplication of two non-zero numbers is non-zero.
   This is an axiom. We will not be proving it since it is a property of
   multiplication and we did not define multiplication ourselves.
 */
lemma {:axiom} non_zero_mul(x:real)
  requires x != 0.0;
  ensures x*x != 0.0;

/*
   This lemma establishes one of the properties of exp that we use.
   You will need to complete its proof in part 4 of the problem.
 */
lemma exp_even (x:real, n:nat)
  requires n % 2 == 0;
  ensures (exp (x, n) == exp (x*x, n/2));
{
  // This tells Dafny to pretend as though this lemma is proven.
  // REPLACE WITH PROOF
  assume(false);
}

/*
   This lemma establishes one of the properties of exp that we use.
   You will need to complete its proof in part 4 of the problem.
 */
lemma exp_odd(x:real, n:nat)
  requires n % 2 == 1;
  ensures (exp (x, n) == exp (x*x, (n-1)/2)*x);
{
  // This tells Dafny to pretend as though this lemma is proven.
  // REPLACE WITH PROOF
  assume (false);
}

/***********************************************************************/
/*                            PARTS 2+3                                */
/***********************************************************************/

/* Specify and verify the following method  */
method exp_by_sqr (x0: real, n0: nat) returns (r: real)
{
  if (x0 == 0.0) { return 0.0; }
  if (n0 == 0) { return 1.0; }
  var x, n, y  := x0, n0, 1.0;
  while (n > 1)
  {
    if (n % 2 == 0)
    {
      x := x * x;
      n := n / 2;
    }
    else
    {
      y := x * y;
      x := x * x;
      n := (n-1)/2;
    }
  }
  return x * y;
}

/***********************************************************************/
/*                            PARTS 4                                  */
/***********************************************************************/

// Prove the lemmas above by replacing assume(false) in lemma body by
// a corresponding proof.




