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
  else add(x, y-1) + 1
}

/* Lemma: x + 0 == 0 */
lemma add_zero_lemma (x: nat)
  ensures add(x, 0) == x;
{
  // Dafny can prove the post-condition directly, nothing for us to do
  assert(add(x, 0) == x);
}


/* Lemma 0 + x == x
   Hint: try different specific cases, then use induction
 */
lemma zero_add_lemma (x: nat)
  ensures add(0, x) == x;
{
  if (x == 0) { }
  else if (x == 1) { }
  else if (x == 2) { }
  else {
    calc {
      add(0, x);
      // expand definition of add and simplify
      add(0, x - 1) + 1;
      {
        // recursively call the lemma
        // Dafny will check that the application is well-defined
        zero_add_lemma(x-1);
        // at this point we have:
        // assume(add(0,x-1) == x-1)
      }
      x - 1 + 1;
      x;
    }
  }
}

/** Lemma: (x + y) + 1 == x + (y + 1) */
lemma add_plus_one (x: nat, y: nat)
  ensures add(x, y) + 1 == add(x, y + 1);
{
  if (y == 0) {}
  else {
    calc {
      add(x, y) + 1;
      // apply definition of add() in reverse
      add(x, y + 1);
    }
  }
}

/** Lemma: (x + y) + 1 == (x + 1) + y */
lemma one_plus_add (x: nat, y: nat)
  ensures add(x, y) + 1 == add(x + 1, y)
{
  if (x == 0) { }
  else if (y == 0) { }
  else {
    calc {
     add(x, y) + 1;
     add(x, y - 1) + 1 + 1;
     { one_plus_add(x, y-1); }
     add(x + 1, y - 1) + 1;
     add(x + 1, y);
    }
  }
}

/** Lemma: (x + y) == (y + x)

   This is the big one to prove
*/
lemma add_comm_lemma (x: nat, y: nat)
  ensures add(x, y) == add(y, x);
{
  if (x == 0) {}
  else if (y == 0) {}
  else if (x == 1 && y == 1) {}
  else {
    calc {
      add(x, y);
      add(x, y - 1) + 1;
      {add_comm_lemma(x, y-1);}
      add(y-1, x) + 1;
      {one_plus_add(y-1, x);}
      add(y, x);
    }
  }
}
