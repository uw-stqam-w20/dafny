/* in class version of the problem. See fast_exp.prob.dfy for details */
/**
   Define function exp for computing an exponent of the number. Use the facts that
   exp(0, n) == 1  if n > 0
   exp(x, 0) == 1
   exp(x, 1) == x
   exp(x, n) == x*exp(x, n-1)
   */
function exp(x: real, n:nat) : real
  // YOUR SPEC HERE (might be empty)
{
  // YOUR CODE HERE
}

/***********************************************************************/
/*                            PARTS 2+3                                */
/***********************************************************************/

/* Specify and verify the following method  */
method exp_by_sqr (x0: real, n0: nat) returns (r: real)
{
  if (n0 == 0) { return 1.0; }
  if (x0 == 0.0) { return 0.0; }
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
/*                            LEMMAS                                   */
/***********************************************************************/
// lemma {:axiom} non_zero_mul(x:real)
//   requires x != 0.0;
//   ensures x*x != 0.0;

//   lemma exp_even (x:real, n:nat)
//     requires n % 2 == 0;
//     ensures (exp (x, n) == exp (x*x, n/2));
//   {
//     // This tells Dafny to pretend as though this lemma is proven.
//     // REPLACE WITH PROOF
//     assume(false);
//   }

//   lemma exp_odd(x:real, n:nat)
//     requires n % 2 == 1;
//     ensures (exp (x, n) == exp (x*x, (n-1)/2)*x);
//   {
//     // This tells Dafny to pretend as though this lemma is proven.
//     // REPLACE WITH PROOF
//     assume (false);
//   }




/***********************************************************************/
/*                            PARTS 4                                  */
/***********************************************************************/

// Prove the lemmas above by replacing assume(false) in lemma body by
// a corresponding proof.




