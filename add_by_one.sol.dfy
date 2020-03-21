/**
   Slow addition by increment. Assume we are only allowed to use increment by a
   constant 1. We would to implement a method that adds two numbers by
   increment.

   Implement, specify, and verify such a method
   */
method add_by_inc(n: nat, m: nat) returns (r: nat)
  ensures r == m + n;
{
  r := n;
  var i := 0;
  while i < m
    invariant i <= m;
    invariant r == n + i;
  {
    i := i + 1;
    r := r + 1;
  }
  return r;
}


/* Extend the implementation above to handle arbitrary integers. That is,
   both arguments might be negative */

method add_by_inc_int(n : int, m : int) returns (r : int)
  ensures r == m + n;
{
  r := n;
  var sign := if m < 0 then -1 else 1;
  var m0 := if m < 0 then -m else m;

  var i := 0;
  while (i < m0)
    invariant i <= m0;
    // if m is negative, r is decreasing
    invariant m < 0 ==> r == n - i;
    // if m is positive, r is increasing
    invariant m >= 0 ==> r == n + i;
  {
    i := i + 1;
    r := r + sign;
  }
}
