/*
   Find an item in an array.

   The goal of this exercise is to specify and verify a function Find that does
   linear search for an item in an array.


   (1) Implement and specify a method Find. This includes an implementation that
       can be executed and a complete specification. At this point, though, the
       specification will not be yet verified.

   (2) Complete the verification of the Find method from part (b). This requires providing
       the necessary inductive invariant for each loop and ranking arguments (where necessary)
       to ensure that each loop terminates and the function computes the desired result.
 */

/**
   Determines whether an element `key` is inside the array `a`.
   If `key` is in `a`, returns the index of key in `a`.
   Otherwise, returns a negative value
 */
method Find(a: array<int>, key : int)  returns (index : int)
  // if index is positive, then key is at that location
  ensures 0 <= index < a.Length ==> a[index] == key;
  // if index is negative, there is no key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
  // index is bounded above by array length
  ensures index < a.Length;
  // find the first occurrence of key in a
  ensures index >= 0 ==> forall j :: 0 <= j < index ==> a[j] != key;
{
  var i := 0;
  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall j :: 0 <= j < i ==> a[j] != key;
  {
    if (a[i] == key) {return i;}
    i := i + 1;
  }
  return -1;
}

method TestFind() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 4;
  a[2] := 2;
  a[3] := 44;

  var v := Find(a, 4);
  assert(v < a.Length);
  if (v >= 0) { assert(a[v] == 4); }
}



/* No solution is provided for this exercise */
method FindLast(a : array<int>, key : int) returns (index : int)
  // YOUR SPEC HERE
{
  // YOUR CODE HERE
}
