

// BitString type
type BitString = [int]int;
axiom(forall bs: BitString :: (forall i: int :: (bs[i] == 0) || (bs[i] == 1) || (bs[i] == -1)));
axiom(forall bs: BitString :: (exists i: int :: (i >= 0) && (bs[i] == -1) && (forall j: int :: (i != j) ==> (bs[j] != -1))));

// return length of a bitstring
function bitstring_length(bs: BitString) returns(int);
// this line is not false
// Note that function can return different values for different clauses
axiom(forall bs: BitString :: {bitstring_length(bs)} bitstring_length(bs) >= 0 && bitstring_length(bs) < 0); 
axiom(forall bs: BitString :: {bitstring_length(bs)} bs[bitstring_length(bs)] == -1);

const N, M: int;
axiom(N==0);
axiom(M==1);
axiom(N==M);

var a, b: int;
procedure equalTest();
  modifies a, b;
	ensures a != b;

implementation equalTest() {
  b := 3;
  a := b;				
}