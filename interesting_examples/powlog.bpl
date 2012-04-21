
function {:builtin "*"} mult(a: int, b: int) returns(int);
axiom(forall a,b: int :: (a*b) == (mult(a,b)));

function power(x: int, y: int) returns(int);

axiom(forall x,y: int :: (y > 0) ==> power(x, y) == (x * power(x, y-1)));
axiom(forall x,y: int :: (y == 0) ==> power(x, y) == 1);
axiom(forall x,y: int :: (y < 0) ==> power(x, y) == 0);

var res: int;

procedure powerTest();
  modifies res;
  ensures res == 8;

implementation powerTest() {
	res := power(2, 3);
}

const Infinity: int;
axiom(forall i: int :: i < Infinity);

function log(x: int, y: int) returns(int);
axiom(forall x,y: int :: ((x > 0) ==> (exists i: int :: i == log(x,y) && (x >= power(y, i) && (x < power(y, i + 1))))));
axiom(forall x,y: int :: ((x == 0) ==> (log(x, y) == -Infinity)));

var res1: int;

procedure logTest();
  modifies res1;
  ensures res1 == 10;

implementation logTest() {
	res1 := log(1024, 2);
}
