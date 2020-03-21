/*
   Find a maximal array element.

   The goal of this exercise is to specify and verify a function Find that does
   linear search for a maximal element in an array.


   (1) Implement and specify a method FindMax. This includes an implementation that
   can be executed and a complete specification. At this point, though, the
   specification will not be yet verified.

   (2) Complete the verification of the FindMax method from part (b). This requires providing
   the necessary inductive invariant for each loop and ranking arguments (where necessary)
   to ensure that each loop terminates and the function computes the desired result.

   (3) Repeat (1) and (2) for FindMaxVal that returns the maximum value
 */

/**
   Return the index of the largest element of a given array
 */
method FindMax(a: array<int>) returns (idx: int)
  requires a.Length >= 1;
  ensures 0 <= idx < a.Length;
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[idx]; 
{
  var i := 1;
  idx := 0;
  var max := a[idx];
  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant 0 <= idx < i;
    invariant max == a[idx];
    invariant forall k :: 0 <= k < i ==> max >= a[k];
  {
    if (a[i] >= max) {
      idx := i;
      max := a[idx];
    }
    i := i + 1;
  }
  return idx;
}


/**
 * Find the maximal value of an array
 */
method FindMaxVal(a: array<int>) returns (val: int)
  requires a.Length >= 1;
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= val;
  ensures exists j :: 0 <= j < a.Length && a[j] == val;
{
  var i := 0;
  val := a[0];
  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall j :: 0 <= j < i ==> a[j] <= val;
    invariant exists j :: 0 <= j < a.Length && a[j] == val;
  {
    if (a[i] >= val)
    {
      val := a[i];
    }
    i := i + 1;
  }
  return val;
}

