

function {:builtin "div"} division(a: int, b: int) returns(int);
axiom(forall a,b: int :: division(a,b) == a / b);

function f(x: int) returns(int);
axiom(forall i: int :: f(i) > 0);


const c: int;

procedure testF();
  ensures c == 0;

implementation testF() {

  var c1, c2: int;

  c1 := 2 / c;
	c2 := 3 / c;

	assume(c1 == 1);
	assume(c2 == 0);

}