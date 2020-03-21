/**
   Use Dafny to prove the following lemmas.
   Whenever possible, use calculational style proof using `calc` block.

   K.R.M Leino and N. Polikarpova. Verified Calculation
   https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml231.pdf
*/

/** Recursive definition of addition.

   We will prove properties of this function
   */
function add (x: nat, y: nat): nat
{
  if (y == 0) then x
  else add (x, y-1) + 1
}

/* Lemma: x + 0 == 0 */
lemma add_zero_lemma (x: nat)
  ensures add (x, 0) == x;
{
  // REPLACE BY PROOF
  assume(false);
}


/* Lemma 0 + x == x
   Hint: try different specific cases, then use induction
 */
lemma zero_add_lemma (x: nat)
  ensures add (0, x) == x;
{
  // REPLACE BY PROOF
  assume(false);
}

/** Lemma: (x + y) + 1 == x + (y + 1) */
lemma add_plus_one (x: nat, y: nat)
  ensures add(x, y) + 1 == add(x, y+1);
{
  // REPLACE BY PROOF
  assume(false);
}

/** Lemma: (x + y) + 1 == (x + 1) + y */
lemma one_plus_add (x: nat, y: nat)
  ensures add(x, y) + 1 == add (x+1, y)
{
  // REPLACE BY PROOF
  assume(false);
}

/** Lemma: (x + y) == (y + x)

   This is the big one to prove
*/
lemma add_comm_lemma (x: nat, y: nat)
  ensures add(x, y) == add(y, x);
{
  // REPLACE BY PROOF
  assume(false);
}
