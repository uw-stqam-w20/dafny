/**
   A factorial of a natural number n, written n!, is the product of all natural numbers less than n.
   For example, 5! = 1*2*3*4*5.
   https://en.wikipedia.org/wiki/Factorial

   The goal of this exercise is to specify and verify a function to compute a
   factorial of a given number.

   This involves three steps

   (1) Formally define a (recursive) mathematical function for computing a factorial.
   The function must be well-defined. That is, for each input, it must produce a correct output.
   The function might be not defined for certain inputs (for example, not defined for
   negative numbers), but must formally state the domain on which it is defined.

   (2) Implement and specify a method to compute Factorial using a loop. This includes an
   implementation that can be executed and a complete specification. At this point, though,
   the specification will not be yet verified.

   (3) Complete the verification of the Factorial method from part (b). This requires providing
   the necessary inductive invariant for each loop and ranking arguments (where necessary)
   to ensure that each loop terminates and the function computes the desired result.
  */

/***********************************************************************/
/*                            PART 1                                   */
/***********************************************************************/

/*
   Define a recursive function, called factorial, that computes n! for a given number n
   (a) 1! = 1
   (b) n! = n*(n-1)! for n > 1
*/
function factorial (n :nat) : nat
  // YOUR SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}

/***********************************************************************/
/*                            PARTS 2 and 3                            */
/***********************************************************************/

/*
   Part 2: Implement and specify method Factorial that takes a natural number and computes
   its factorial.

   Part 3: Complete the verification of the function Factorial by providing the necessary
   inductive invariant and ranking argument.
 */

method Factorial (n: nat) returns (v:nat)
  // YOUR SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}


/***********************************************************************/
/*                            PARTS 4 (BONUS)                          */
/***********************************************************************/

/*
   Specify and verify the following implementation of Factorial that is taken from

   A. Turing. Checking a Large Routine
   http://www.turingarchive.org/browse.php/b/8

   F.L. Moris and C.B. Jones. An Early Proof by Alan Turing
   https://ieeexplore.ieee.org/document/4640518
 */

method FactorialTuring(n: nat) returns (v: nat)
  requires n > 0;
  ensures v == fact(n);
{
  var r := 1;
  var u := 1;

  while (true)
  {
    v := u;
    if (r - n >= 0)
    { return v; }
    var s := 1;
    while (true)
    {
      u := u + v;
      s := s + 1;
      if ((s - (r + 1)) >= 0)
      {
        break;
      }
    }
    r := r + 1;
  }
}


































/**
method factorial_turing (n: int) returns (v: int)
  requires n > 0;
  ensures v == fact(n);
{
  var r := 1;
  var u := 1;

  while (true)
  {
    v := u;
    if (r - n >= 0)
    { return v; }
    var s := 1;
    while (true)
    {
      u := u + v;
      s := s + 1;
      if ((s - (r + 1)) >= 0)
      {
        break;
      }
    }
    r := r + 1;
  }
}
*/
