function {:builtin "div"} divide(a: int, b: int) returns(int);
function {:builtin "*"} mult(a: int, b: int) returns(int);

var c: int;
procedure try1(a: int, b: int);
  requires a>0 && b>0 && a < b;
	modifies c;
	ensures c == 0;

implementation try1(a: int, b: int) {
  c := divide(a, b);
}

procedure try2(a: int, b: int);
  requires a==10 && b==2;
	modifies c;
	ensures c == 5;

implementation try2(a: int, b: int) {
  c := 3;
  c := divide(10, 2);
}

var d: int;
procedure try3();
	modifies d;
	ensures d == 10;

implementation try3() {
  d := mult(5, 2);
}

var e: int;
procedure try4(a: int, b: int);
  requires a > 0 && b > 0;
	modifies e;
	ensures e > a && e > b;

implementation try4(a: int, b: int) {
  e := mult(a, b);
}

