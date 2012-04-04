
const N: int;
axiom N > 0;

var min: int;

procedure findMin(arr: [int]int);
  modifies min;
  ensures (forall i: int :: (i >= 0 && i < N) ==> min <= arr[i]);
  ensures (exists i: int :: arr[i] == min);

implementation findMin(arr: [int]int) {

  var n: int;

  min := arr[0];
  n := 1;
  
  while(n < N) 
  invariant n > 0 && n <= N;
  invariant (forall i: int :: (i >= 0 && i < n) ==> min <= arr[i]);
  invariant (exists i: int :: i >= 0 && i < n && min == arr[i]);
  {
    if(arr[n] <= min) {
      min := arr[n];
    }
    n := n + 1;
  }
  
}
    
    