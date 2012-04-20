

function summation(A: [int]int, i: int) returns(int);

axiom(forall A: [int]int, i: int :: summation(A, i) == (A[i] + summation(A, i-1)));
axiom(forall A: [int]int, i: int :: (i < 0) ==> summation(A, i) == 0);

var arr: [int]int;

procedure summationTest();
  modifies arr;
  ensures summation(arr,1) == 4;

implementation summationTest() {
  arr[0] := 1;
	arr[1] := 2;

}