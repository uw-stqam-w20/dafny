/**
   This is an in-class version of the problem.
   See gcd.prob.dfy for complete problem description.
 */
/*
   (a) gcd(n, n) == n
   (b) gcd(m, n) == gcd(m-n, n) whenever m > n
   (c) gcd(m, n) == gcd(m, n-m) whenever n > m
 */
function gcd(m: nat, n: nat): nat
  // EXTRA SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}



method GcdCalc(m: nat, n:nat) returns (res :nat)
  // YOUR SPEC GOES HERE
{
  // YOUR CODE GOES HERE
}












/*
method GcdCal(m: nat, n: nat) returns (res: nat)
  ensures res == gcd(m, n);
{
  var m1: nat, n1: nat := m, n;

  while (m1 != n1)
  {
    if (m1 > n1) {
      m1 := m1 - n1;
    }
    else {
      n1 := n1 - m1;
    }
 }
 return m1;
}
 */









/* gcd lemma: use gcd(m, n) = gcd(n1, m1) */
