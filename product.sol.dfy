/* Solution. See product.prob.dfy for problem statement */
/**
   Slow multiplication by addition.

   Verify the methods provided below. For each method, specify the necessary inductive
   invariants and ranking functions. Ranking functions must be specified even if Dafny
   can figure them out automatically. That is, do not delete 'decreases' keywords.
*/

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

/***********************************************************************/
/* ALTERNATIVE SOLUTION USING GHOST VARIABLES                          */
/***********************************************************************/
method ProductGhost(m: nat, n: nat) returns (res: nat)
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
    // -- value of res before the inner loop
    ghost var pre_res := res;
    while (n1 != 0)
      invariant n1 >= 0;
      invariant res == pre_res + (n-n1);
      decreases n1;
    {
      res := res+1;
      n1 := n1-1;
    }
    m1 := m1-1;
  }
}

// Using ghost variables idea from the ALTERNATIVE solution above
method ProductThree(m: nat, n: nat, p: nat) returns (res: nat)
  ensures res == m*n*p;
{
  var m1: nat := 0;
  res := 0;

  while (m1!=m)
    invariant m1 <= m;
    invariant res == m1*n*p;
    decreases m - m1;
  {
    var n1: nat := 0;
    ghost var res_l2 := res;
    while (n1!=n)
      invariant n1 <= n;
      invariant res == res_l2 + n1*p;
      decreases n - n1;
    {
      var p1: nat := 0;
      ghost var res_l3 := res;
      while (p1!=p)
        invariant p1 <= p;
        invariant res == res_l3 + p1;
        decreases p - p1;
      {
        res := res+1;
        p1 := p1+1;
      }
      n1 := n1+1;
    }
    m1:= m1+1;
  }
}


