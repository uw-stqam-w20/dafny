/** Bubble sort is one of the simplest sort algorithms.
   https://en.wikipedia.org/wiki/Bubble_sort

   The goal of this exercise is to specify, implement, and verify an implementation of Bubble sort.
*/


/** Specify, implement, and verify */
method bubbleSort (a: array<int>)
  requires true; // PRE-CONDITIONS 
  ensures true; // POST-CONDITIONS
  modifies a;
{
  // YOUR IMPLEMENTATION
}


































/*
method bubbleSort (a: array<int>)
  modifies a;
{
  var i:nat := 1;

  while (i < a.Length)
  {
    var j:nat := i;
    while (j > 0)
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
*/

/** inner invariant
   invariant 0 <= j <= i;
   invariant forall u, v :: 0 <= u < v < j ==> a[u] <= a[v];
   invariant forall u, v :: 0 <= u < j < v <= i ==> a[u] <= a[v];
   invariant forall u, v :: j <= u < v <= i ==> a[u] <= a[v];
 */

/** outer invariant

   invariant i <= a.Length;
   invariant forall u, v :: 0 <= u < v < i ==> a[u] <= a[v];
 */
