
var A: [int]int;

procedure trial();
  modifies A;
  ensures (forall i: int :: i>=0 && A[i] < A[i+1]);

implementation trial() {
  var i: int;
  
  A[0] := 0;
  i := 0;
  while(true) {
    A[i+1] := A[i] + 1;
  }
}