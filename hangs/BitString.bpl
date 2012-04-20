function {:builtin "*"} mult(a: int, b: int) returns(int);
function {:builtin "rem"} remainder(a: int, b: int) returns(int);
function {:builtin "div"} division(a: int, b: int) returns(int);
function {:builtin "mod"} modulo(a: int, b: int) returns(int);

// BitString type
type BitString = [int]int;
axiom(forall bs: BitString :: (forall i: int :: (bs[i] == 0) || (bs[i] == 1) || (bs[i] == -1)));
axiom(forall bs: BitString :: (exists i: int :: (i >= 0) && (bs[i] == -1) && (forall j: int :: (i != j) ==> (bs[j] != -1))));

function bitstring_length(bs: BitString) returns(int);
axiom(forall bs: BitString :: {bitstring_length(bs)} bitstring_length(bs) >= 0);
axiom(forall bs: BitString :: {bitstring_length(bs)} bs[bitstring_length(bs)] == -1);

// debinarize an integer (111 --> 7)
function debinarize(bs: BitString) returns(int);
axiom(forall bs: BitString :: debinarize(bs) >= 0);
axiom(forall bs: BitString :: (exists cs: BitString:: (forall i: int:: (i>=0 && i<bitstring_length(bs)) ==> bs[i+1] == cs[i]) && (debinarize(bs) == (bs[0] + mult(2, debinarize(cs))))));
axiom(forall bs: BitString :: bs[0]==-1 ==> debinarize(bs) == 0);

// binarize an integer (3 --> 011)
// function binarize(num: int) returns(BitString);
// axiom(forall n: int :: n>=0 ==> debinarize(binarize(n)) == n);

var res: int;
procedure testLength();
  modifies res;
	ensures res==2;

implementation testLength() {
  var A: BitString;
	A[0] := 1;
	A[1] := 1;
	A[2] := -1;
	A[3] := 0;
	res := bitstring_length(A);
}

