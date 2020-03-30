/**
   Dafny reduces any program given to it to a FOL formula(s) that are solved by
   SMT solver (Z3). These formulas are called Verification Conditions (or VC for
   short). In this file, we illustrate this reduction. We will reduce each
   program to a program that has only bounded executions (i.e., no loops or
   function calls), but uses extra assume() and assert() statements.

   You already know how to convert programs like that to Z3. For example, you
   can use the symbolic execution engine you have developed as part of
   Assignment 2!

   The main reason for this exercise is to help you debug verification attempts.
   When verification goes wrong, you can debug it by slowly converting the
   program to the simplest form as a VC and narrow down the exact source of the
   problem.
 */
method add_by_inc_vc(n: nat, m: nat) returns (r: nat)
  ensures r == m + n;
{
  assume (true); // requires true
  r := n;
  var i := 0;
  assert (i <= m && r == n + i); // checks that inv is true before the loop is entered
  // havoc i, r;
  i, r := *, *;
  assume (i <= m && r == n + i);
  if ( i < m )
    // invariant i <= m && r == n + i;
    //decreases m - i;
  {
    ghost var rank0 := m - i;
    i := i + 1;
    r := r + 1;
    assert(i <= m && r == n + i);
    assert(m - i < rank0);
    ghost var rank1 := m - i;
    assert(rank1 < rank0);
    assert(rank1 >= 0);
    assume(false);
  }

  assert(r == m + n);
  return r;
}

