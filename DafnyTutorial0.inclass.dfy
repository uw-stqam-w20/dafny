method Abs(x: int) returns (y: int)
{
  if x < 0
  { return -x; }
  else
  { return x; }
}

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
{
  more := x + y;
  less := x - y;
  // comments: are not strictly necessary.
}

// Exercise 0. Write a method Max that takes two integer parameters and returns
// their maximum. Add appropriate annotations and make sure your code verifies.
method Max(a: int, b:int) returns (c: int)
{
  if (a < b) { return b; } else { return a; }
}

/*
// use definition of Abs() from before.
method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
  // -- this assertion fails. Refine ensures of Abs to fix it
  assert v == 3;
}
*/

function abs(x: int): int
{
  if x < 0 then -x else x
}

// Exercise 4. Write a function max that returns the larger of two given integer
// parameters. Write a test method using an assert that checks that your
// function is correct.
function max(a: int, b: int) : int
{
  if a < b then b else a
}

method TerminationTest()
{
  // let i be an arbitrary positive number
  var i := *;
  assume(i > 0);

  while ( 0 < i )
    invariant 0 <= i;
    // ranking function: decreasing measure
    decreases i;
  {
    i := i - 1;
  }
}

/*********************************************************************************/
/* TRY OTHER EXERCISES THAT DO NOT INVOLVE ARRAYS THEN COME BACK TO THE TUTORIAL */
/*********************************************************************************/
