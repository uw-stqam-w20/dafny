/** Solution: see gcd_prob.dfy for the problem statement */
function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0;
  decreases m + n;
{
  if (m == n) then m
  else if (m > n) then gcd(m - n, n)
  else gcd(m, n - m)
}
method GcdCalc(m: nat, n: nat) returns (res: nat)
  requires m > 0 && n > 0;
  ensures res == gcd(m, n);
{
  var n1, m1 := n, m;
  while (n1 != m1)
    decreases m1 + n1;
    invariant m1 > 0 && n1 > 0;
    invariant gcd(m, n) == gcd(m1, n1);
  {
    if (m1 < n1) {
     n1 := n1 - m1;
    } else {
     m1 := m1 - n1;
    }
  }
  assert(m1 == n1);
  return n1;
}
