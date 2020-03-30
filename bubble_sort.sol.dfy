/** Bubble sort is one of the simplest sort algorithms.
   https://en.wikipedia.org/wiki/Bubble_sort

   The goal of this exercise is to specify, implement, and verify an implementation of Bubble sort.
*/
predicate sorted(a:array<int>, from:int, to:int)
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

/** Specify, implement, and verify */
method bubbleSort (a: array<int>)
  requires  a.Length > 0;
  ensures forall u, v :: 0 <= u < v < a.Length ==> a[u] <= a[v];
  modifies a;
{
  var i:nat := 1;

  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall u, v :: 0 <= u < v < i ==> a[u] <= a[v];
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant forall u, v :: 0 <= u < v < j ==> a[u] <= a[v];
      invariant forall u, v :: 0 <= u < j < v <= i ==> a[u] <= a[v];
      invariant forall u, v :: j <= u < v <= i ==> a[u] <= a[v];
    {
      if (a[j-1] > a[j]) {
        // Swap a[j-1] and a[j]
        var temp := a[j-1];
        a[j] := temp;
        a[j-1] := a[j];
     }
      j := j - 1;
    }
    i := i+1;
  }
}

/* also checks that bubbleSort2() preserves the elements, not just returns a sorted array */
method bubbleSort2 (a: array<int>)
  requires  a.Length > 0;
  ensures forall u, v :: 0 <= u < v < a.Length ==> a[u] <= a[v];
  ensures multiset(a[..]) == multiset(old(a[..]));
  modifies a;
{
  var i:nat := 1;

  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall u, v :: 0 <= u < v < i ==> a[u] <= a[v];
    invariant multiset(a[..]) == multiset(old(a[..]));
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant forall u, v :: 0 <= u < v < j ==> a[u] <= a[v];
      invariant forall u, v :: 0 <= u < j < v <= i ==> a[u] <= a[v];
      invariant forall u, v :: j <= u < v <= i ==> a[u] <= a[v];
      invariant multiset(a[..]) == multiset(old(a[..]));
    {
      if (a[j-1] > a[j]) {
        // Swap a[j-1] and a[j]
        var temp := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i+1;
  }
}


/********************************************************************************************/
/**
   The example above uses Dafny builtin theory of multisets. The example below
   shows how to achieve the same result from first principles.

   This requires defining a notion of permutation in FOL. Teaching Dafny a few
   lemmas about permutations, and then applying these lemmas in the main prove.

   The formalization uses a new datatype `seq<T>` that represents a sequence --
   an immutable sequence of elements of a given type T. For example, `seq<int>` is
   a sequence of integers. Think of a sequence as Java Strings or Python tuples.
   They are similar to array or lists, but are immutable. In Dafny syntax, if `A`
   is an array, then `A[..]` is a sequence representing the content of the array.
 */
/********************************************************************************************/

/**
   Returns number of occurrences of a given value `val` in size a given sequence
 */
function count(a:seq<int>, val:int): nat
{
  if |a| == 0 then 0
  else
    if a[0] == val then 1 + count(a[1..], val)
    else count(a[1..], val)
}

/**
   A sequence `b` is a permutation of sequence `a` if every integer `v` has
   exactly the same number of occurrences in `a` and in `b`
 */
predicate perm(a: seq<int> , b:seq<int>)
{
  forall v :: count(a, v) == count(b, v)
}


/** Permutation is transitive.
   Dafny can prove that automatically.
 */
lemma trans_perm(a:seq<int>, b:seq<int>, c:seq<int>)
  requires perm(a, b) && perm(b, c);
  ensures perm(a, c);
{}

/** Permutation is commutative.
    Dafny can prove that automatically.
  */
lemma comm_perm(a:seq<int> , b:seq<int> )
  requires perm(a, b);
  ensures perm(b, a);
{}

/**
   If sequences `a` and `b` differ only in two positions, and the values in
   these to positions are swapped, then sequences are permutations of one
   another.

   This is assumed without a prove. Completing the prove is left as an exercise.

 */
lemma swap_lemma(a: seq<int>, b:seq<int>, pos1:nat, pos2:nat)
  requires |a| == |b|;
  requires 0 <= pos1 < pos2 < |a|;
  requires forall k :: 0 <= k < |a| && k != pos1 && k != pos2 ==> a[k] == b[k];
  requires a[pos1] == b[pos2];
  requires a[pos2] == b[pos1];
  ensures perm(a, b);
  { assume(false); }

/** A helper method to swap two positions in an array */
method swap(a: array<int>, pos1:nat, pos2:nat)
  modifies a;
  requires 0 <= pos1 < pos2 < a.Length;
  ensures forall k :: 0 <= k < a.Length && k != pos1 && k != pos2 ==> a[k] == old(a[k]);
  ensures a[pos1] == old(a[pos2]);
  ensures a[pos2] == old(a[pos1]);
{
  var temp := a[pos2];
  a[pos2] := a[pos1];
  a[pos1] := temp;
}

/**
   Verified version of bubble sort, in which the prove that the output is
   permutation of the input is done explicitly without using any special help
   from Dafny.
 */
method bubbleSort3 (a: array<int>)
  requires  a.Length > 0;
  ensures forall u, v :: 0 <= u < v < a.Length ==> a[u] <= a[v];
  ensures perm(a[..], old(a[..]));
  modifies a;
{
  var i:nat := 1;

  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall u, v :: 0 <= u < v < i ==> a[u] <= a[v];
    invariant perm(a[..], old(a[..]));
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant forall u, v :: 0 <= u < v < j ==> a[u] <= a[v];
      invariant forall u, v :: 0 <= u < j < v <= i ==> a[u] <= a[v];
      invariant forall u, v :: j <= u < v <= i ==> a[u] <= a[v];
      invariant perm(a[..], old(a[..]));
    {
      ghost var old_a := a[..];
      if (a[j-1] > a[j]) {
        // Swap a[j-1] and a[j]
        swap(a, j-1, j);
        swap_lemma(old_a, a[..], j-1, j);
        comm_perm(old_a, a[..]);
      }
      j := j - 1;

      trans_perm(a[..], old_a, old(a[..]));
      assert(perm(a[..], old(a[..])));
    }
    i := i+1;
  }
}


/**
   In addition to showing that an algorithm is correct, we can also prove upper
   bound on its complexity.

   In this example, we show that bubbleSort running time is bounded by |a|^2,
   hence the algorithm is in O(|a|^2)
   */
method bubbleSort4 (a: array<int>)
  requires  a.Length > 0;
  ensures forall u, v :: 0 <= u < v < a.Length ==> a[u] <= a[v];
  modifies a;
{
  // counter that counts number of executions of the main loop
  var cnt := 0;
  var i:nat := 1;

  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall u, v :: 0 <= u < v < i ==> a[u] <= a[v];
    invariant cnt <= a.Length * i;
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant forall u, v :: 0 <= u < v < j ==> a[u] <= a[v];
      invariant forall u, v :: 0 <= u < j < v <= i ==> a[u] <= a[v];
      invariant forall u, v :: j <= u < v <= i ==> a[u] <= a[v];
      invariant cnt <= a.Length * i + (i-j);
    {
      if (a[j-1] > a[j]) {
        // Swap a[j-1] and a[j]
        var temp := a[j-1];
        a[j] := temp;
        a[j-1] := a[j];
      }
      j := j - 1;
      // increment count each iteration of the loop
      cnt := cnt + 1;
    }
    i := i+1;
  }
  // claim that cnt is bounded above by |a|^2
  assert(cnt <= a.Length * a.Length);
}

