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
method add_by_inc(n: nat, m: nat) returns (r: nat)
  ensures r == m + n;
{
  r := n;
  var i := 0;
  while i < m
    invariant i <= m;
    invariant r == n + i;
    decreases m - i;
  {
    i := i + 1;
    r := r + 1;
  }
  return r;
}

/* VC for method above */
method add_by_inc_Vc(n: nat, m: nat) returns (r: nat)
{
  // instead of requires
  assume(true);
  r := n;
  var i := 0;

  // check that invariant is true before the loop
  assert(i <= m);
  assert(r == n + i);
  // havoc all variables that are assigned in the loop
  // '*' stands for non-deterministic value
  i, r := *, *;
  // assume inductive invariant before loop body
  assume(i <= m);
  assume(r == n + i);
  if (i < m)
  {
   // store value of ranking function
    ghost var rank0 := (m - i);
    i := i + 1;
    r := r + 1;
    // check inductive invariant after loop body
    assert(i <= m);
    assert(r == n + i);
    // recompute ranking function
    ghost var rank := (m - i);
    // ranking function is decreasing
    assert(rank < rank0);
    // ranking function is bounded below by 0 
    assert(rank >= 0);
     // -- tells verifier that nothing flows out of this loop
    assume(false);
  }
  // instead of ensures
  assert r == m + n;
}



method Product(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
{
  var m1: nat := m;
  res := 0;

  while (m1!=0)
    invariant m1 >= 0;
    invariant res == (m - m1) * n;
    decreases m1;
  {
    var n1: nat := n;
    while (n1 != 0)
      invariant n1 >= 0;
      invariant res == (m - m1) * n + (n-n1);
      decreases n1;
    {
      res := res+1;
      n1 := n1-1;
    }
    m1 := m1-1;
  }
}

// this example show VC of nested loops
// Same pattern as before, but applied twice
method Product_Vc(m: nat, n: nat) returns (res: nat)
{
  assume(true);
  var m1: nat := m;
  res := 0;

  assert(m1 >= 0 && res == (m - m1) * n);
  res, m1 := *, *;
  assume(m1 >= 0 && res == (m - m1) * n);
  if (m1 != 0)
  {
    var rankM0 := m1;
    var n1: nat := n;
    assert(n1 >= 0 && res == (m - m1) * n + (n - n1));
    res, n1 := *, *;
    assume(n1 >= 0 && res == (m - m1) * n + (n - n1));
    if (n1 != 0)
    {
      ghost var rankN0 := n1;
      res := res+1;
      n1 := n1-1;
      assert(n1 >= 0 && res == (m - m1) * n + (n - n1));
      ghost var rankN := n1;
      assert(rankN < rankN0 && rankN >= 0);
      assume(false);
    }
    m1 := m1-1;
    assert(m1 >= 0 && res == (m - m1) * n);
    var rankM := m1;
    assert(rankM < rankM0 && rankM >= 0);
    assume(false);
  }

  assert(res == m*n);
}

