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
    invariant true; // REPLACE BY NECESSARY INVARIANT
    decreases 0; // REPLACE BY NECESSARY RANKING FUNCTION
  {
    var n1: nat := n;
    while (n1 != 0)
      invariant true; // REPLACE BY NECESSARY INVARIANT
      decreases 0; // REPLACE BY NECESSARY RANKING FUNCTION
    {
      res := res+1;
      n1 := n1-1;
    }
    m1 := m1-1;
  }
}


method ProductThree(m: nat, n: nat, p: nat) returns (res: nat)
  ensures res == m*n*p;
{
  var m1: nat := 0;
  res := 0;

  while (m1!=m)
    invariant true; // REPLACE BY NECESSARY INVARIANT
    decreases 0; // REPLACE BY NECESSARY RANKING FUNCTION
  {
    var n1: nat := 0;
    while (n1!=n)
      invariant true; // REPLACE BY NECESSARY INVARIANT
      decreases 0; // REPLACE BY NECESSARY RANKING FUNCTION
    {
      var p1: nat := 0;
      while (p1!=p)
        invariant true; // REPLACE BY NECESSARY INVARIANT
        decreases 0; // REPLACE BY NECESSARY RANKING FUNCTION
      {
        res := res+1;
        p1 := p1+1;
      }
      n1 := n1+1;
    }
    m1:= m1+1;
  }
}


