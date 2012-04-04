var x, y, z: int;

var k: int where k > 0;

procedure Trial(n: int);
  modifies x, y;
  ensures x == y;

implementation Trial(n: int)
{
  x := y;
}

procedure Subtraction();
  modifies z;
  ensures z < y;

implementation Subtraction()
{
  z := y - k;
}
