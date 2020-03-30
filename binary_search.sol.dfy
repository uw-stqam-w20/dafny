/** Predicate to increase readability of specifications */
predicate sorted(a: array<int>)
   reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
  // require that an array is non empty and sorted
   requires 0 <= a.Length && sorted(a)
   // if return is positive, desired value is at index
   ensures 0 <= index ==> index < a.Length && a[index] == value
   // if return is negative, the array does not have the value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while (low < high)
    // low and high remain ordered
    invariant 0 <= low <= high <= a.Length
    // all processed entries do not have the value
    invariant forall i ::
    0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value
    {
      low := mid + 1;
    }
    else if value < a[mid]
    {
      high := mid;
    }
    else
    {
      return mid;
    }
  }
  return -1;
}
