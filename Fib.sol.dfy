/** Solution: see Fib.prob..dfy for the problem statement */
/*
   Fibonacci sequence is a well known sequence of numbers, defined by the following equations
   Fn_0 = 0
   Fn_1 = 1
   Fn_i = Fn_{i-1} + Fn_{i-2}
   https://en.wikipedia.org/wiki/Fibonacci_number

   The goal of this exercise is to specify and verify a function to compute a given Fibonacci number.

   This involves three steps

   (1) Formally define a (recursive) mathematical function for computing a Fibonacci number.
       The function must be well-defined. That is, for each input, it must produce a correct output.
       The function might be not defined for certain inputs (for example, not defined for
       negative numbers), but must formally state the domain on which it is defined.

   (2) Implement and specify a method to compute a Fibonacci number using a loop.
       This includes an implementation that can be executed and a complete specification.
       At this point, though, the specification will not be yet verified.

   (3) Complete the verification of the Fib method from part (b). This requires providing
       the necessary inductive invariant for each loop and ranking arguments (where necessary)
       to ensure that each loop terminates and the function computes the desired result.


   */

/***********************************************************************/
/*                            PART 1                                   */
/***********************************************************************/

/*
   Define a recursive function, called fib, that computes a given Fibonacci number.
   Use the following definition:

      fib(0) == 0
      fib(1) == 1
      fib(i) == fib(i-1) + fib(i-2)
*/
function fib (n: nat) : nat
{
  if (n == 0) then 0
  else if (n == 1) then 1
  else fib(n-1) + fib(n-2)
}

/***********************************************************************/
/*                            PARTS 2 and 3                            */
/***********************************************************************/

/*
   Part 2: Implement and specify method Fib that takes a natural numbers as
   input and return the corresponding Fibonacci number.

   Part 3: Complete the verification of the function Fib by providing the necessary
   inductive invariant and ranking argument.
 */
method Fib (n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if (n == 0) { return 0; }
  var a := 0;
  b := 1;

  var i := 1;
  while (i < n)
    invariant i <= n;
    invariant a == fib(i-1);
    invariant b == fib(i);
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
