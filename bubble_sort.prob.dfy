/** Bubble sort is one of the simplest sort algorithms.
   https://en.wikipedia.org/wiki/Bubble_sort

   The goal of this exercise is to specify, implement, and verify an implementation of Bubble sort.
*/


/* sorted: true if the given array is sorted in the range [from, to)

   For example, sorted(a, 0, a.Length) is true if array `a` is sorted
 */
predicate sorted(a:array<int>, from:int, to:int)
  reads a;
{
  true
}

/**
   pivot: true if `pvt` of the given array in the array [0, to)

   An index is a pivot if it divides an array such that all elements with index less than pivot
   are less than all elements with index greater than pivot.

   For example, pivot(a, a.Length, 5) is true if all elements with index less
   than 5 are smaller than all the elements with index greater than 5 in the
   array `a`
 */
predicate pivot(a:array<int>, to:int, pvt:int)
  reads a;
{
  true
}

/** Specify, implement, and verify */
method bubbleSort (a: array<int>)
  requires true; // PRE-CONDITIONS 
  ensures true; // POST-CONDITIONS
  modifies a;
{
  // YOUR IMPLEMENTATION
}


