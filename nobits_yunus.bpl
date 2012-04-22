

function {:builtin "*"} mult(a: int, b: int) returns(int);
axiom(forall x,y: int :: ((x*y) == mult(x, y)));

function {:builtin "div"} division(a: int, b: int) returns(int);
axiom(forall x,y: int :: ((x/y) == division(x, y)));

// Just to specify we have some specific need from this type. i.e. any char is less than 256 and greater than -1.
// We will meet this specifications by using ensures and requires.
type char = int;

// Just to specify we have some specific need from this type. i.e. string is an array composed of char.
// We will meet this specifications by using ensures and requires.
type String = [int]int;

// return length of a string
function length(string: String) returns(int);
axiom(forall string: String :: length(string) >= 0);
axiom(forall string: String :: string[length(string)] == 0);

// compare two strings. return true if they are equal. Otherwise, return false.
function cmpstr(str1: String, str2: String) returns(bool);
axiom(forall str1, str2: String :: cmpstr(str1, str2) ==> ((length(str1) == length(str2)) && (forall i: int :: (i>=0 && i<length(str1)) ==> (str1[i] == str2[i]))));
axiom(forall str1, str2: String :: !cmpstr(str1, str2) ==> ((length(str1) != length(str2)) || (exists i: int :: (i>=0 && i<length(str1)) && (str1[i] != str2[i]))));

// count how many 'c' exists upto 'upper_limit' in 'string'
function count(string: String, 	c: char, upper_limit: int) returns(int);
axiom(forall string: String, c: char, i: int :: (i >= 0 && string[i]==c) ==> (count(string, c, i) == (1 + count(string, c, i-1))));
axiom(forall string: String, c: char, i: int :: (i >= 0 && string[i]!=c) ==> (count(string, c, i) == count(string, c, i-1)));
axiom(forall string: String, c: char, i: int :: (i < 0) ==> (count(string, c, i) == 0));


var Cum: [int]int;
var Tot: int;

procedure encodeAndDecode(string: String) returns(out: String);
  requires (forall j:int :: j >= 0 ==> (string[j] < 256 && string[j] >= 0));
  requires (exists i:int :: (i >= 0 && string[i] == 0) && (forall j:int :: (i != j) ==> (string[j] != 0)));
	modifies Cum, Tot;
	ensures (forall j:int :: j >= 0 ==> (out[j] < 256 && out[j] >= 0));
  ensures (exists i:int :: (i >= 0 && out[i] == 0) && (forall j:int :: (i != j) ==> (out[j] != 0)));
  ensures (cmpstr(string, out));

implementation encodeAndDecode(string: String) returns(out: String) {

  var lo,r0,r: int;
	var i: int;
	var x: int;
	var c: char;
	var len: int;

	len := length(string);
	// Calculate static intervals

	Cum[0] := 0;
	i := 1;
	while (i < 256)
	{
	  Cum[i] := Cum[i-1] + count(string, i, len-1);
		i := i + 1;
	}
	Tot := Cum[i - 1];
	
	
  // ENCODING PART
	lo := 0;
	r0 := 1;

	r := r0;
	while (r == 0)
	{
	  lo := 0;
		r := r0;

		i := 0;
		while (i < len) {
		  lo := lo + ((r * Cum[i]) / Tot);
			r := ((r * Cum[i+1])/Tot) - ((r * Cum[i])/Tot);
		}

		r0 := r0 * 2;
	}


	// DECODING PART
	r := r0 / 2;
	x := lo;
	i := 0;
	while (i < len)
	{
	  c := 0;

		while (((r*c) / Tot) <= x)
		{
				c := c + 1;
		}
		c := c - 1;
		
	  out[i] := c;
	  x := x - ((r * Cum[c]) / Tot);
		r := ((r * Cum[c+1]) / Tot) - ((r * Cum[c]) / Tot);
	  i := i + 1;
	}
	out[i] := 0;
}

