/*
   The greatest common divisor (gcd) of two natural numbers m and n is a number k such that
   (a) k divides m; (b) k divides n; and (c) k is the largest number with these properties.
   https://en.wikipedia.org/wiki/Greatest_common_divisor

   The goal of this exercise is to specify and verify a function to compute GCD of two numbers.
   This involves three steps

   (1) Formally define a (recursive) mathematical function for computing gcd.
       The function must be well-defined. That is, for each input, it must produce a correct output.
       The function might be not defined for certain inputs (for example, not defined for
       negative numbers), but must formally state the domain on which it is defined.

   (2) Implement and specify a method to compute GCD using a loop. This includes an implementation
       that can be executed and a complete specification. At this point, though, the specification
       will not be yet verified.

   (3) Complete the verification of the GCD method from part (b). This requires providing
       the necessary inductive invariant for each loop and ranking arguments (where necessary)
       to ensure that each loop terminates and the function computes the desired result.

 */

/***********************************************************************/
/*                            PART 1                                   */
/***********************************************************************/

/*
   Define a recursive function, called gcd, that computes a GCD of two numbers.
   Use the following properties of gcd.
   (a) gcd(n, n) == n
   (b) gcd(m, n) == gcd(m-n, n) whenever m > n
   (c) gcd(m, n) == gcd(m, n-m) whenever n > m
 */
function gcd(m: nat, n: nat): nat
{
  /** YOUR IMPLEMENTATION GOES HERE */
}



/***********************************************************************/
/*                            PARTS 2 and 3                            */
/***********************************************************************/

/*
   Part 2: Implement and specify method GcdCalc that takes two natural numbers as
   input and returns their GCD.

   Part 3: Complete the verification of the function GcdCalc by providing the necessary
   inductive invariant and ranking argument.
 */

method GcdCalc(m: nat, n:nat) returns (res :nat)
  // YOUR SPEC GOES HERE
{
  // YOUR IMPLEMENTATION GOES HERE
}











