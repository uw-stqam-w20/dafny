/**
   Determines whether an element `key` is inside the array `a`.
   If `key` is in `a`, returns the index of key in `a`.
   Otherwise, returns a negative value
 */
method Find(a: array<int>, key : int)  returns (index : int)
  // YOUR SPEC HERE
{
  // YOUR CODE HERE
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

/**
   Returns the last occurrence of `key` in `a`, or a negative number if no such
   index exists.
  */
method FindLast(a: array<int>, key : int) returns (index : int)
  // YOUR SPEC HERE
{
  // YOUR CODE HERE
}
