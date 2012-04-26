

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
axiom(forall string: String :: {length(string)} length(string) >= 0);
axiom(forall string: String :: {length(string)} string[length(string)] == 0);

// compare two strings. return true if they are equal. Otherwise, return false.
function cmpstr(str1: String, str2: String) returns(bool);
axiom(forall str1, str2: String :: cmpstr(str1, str2) ==> ((length(str1) == length(str2)) && (forall i: int :: (i>=0 && i<length(str1)) ==> (str1[i] == str2[i]))));
axiom(forall str1, str2: String :: !cmpstr(str1, str2) ==> ((length(str1) != length(str2)) || (exists i: int :: (i>=0 && i<length(str1)) && (str1[i] != str2[i]))));

// count how many 'c' exists upto 'upper_limit' in 'string'
function count(string: String, 	c: char, upper_limit: int) returns(int);
axiom(forall string: String, c: char, i: int :: count(string, c, i) >= 0);
axiom(forall string: String, c: char, i: int :: (i < 0) ==> (count(string, c, i) == 0));
axiom(forall string: String, c: char, i: int :: (i >= 0 && string[i]!=c) ==> (count(string, c, i) == count(string, c, i-1)));
axiom(forall string: String, c: char, i: int :: (i >= 0 && string[i]==c) ==> (count(string, c, i) == (1 + count(string, c, i-1))));




// summation of elements in array
function summation(A: [int]int, i: int) returns(int);
axiom(forall A: [int]int, i: int :: {summation(A, i-1)} summation(A, i) == (A[i] + summation(A, i-1)));
axiom(forall A: [int]int, i: int :: (i < 0) ==> summation(A, i) == 0);

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
	var lo_arr, r0_arr, r_arr: [int]int;
	var i: int;
	var x: int;
	var c: char;
	var len: int;
	var deneme: String;

  assume (forall j:int :: j >= 0 ==> (deneme[j] < 256 && deneme[j] >= 0));
  assume (exists k:int :: (k >= 0 && deneme[k] == 0) && (forall j:int :: (k != j) ==> (deneme[j] != 0)));
	assume (deneme[3] == 0);

	len := length(string);
	// Calculate static intervals

	assert(len >= 0);
	assert(string[len]==0);
	assert(length(deneme) == 3);
	assert(count(deneme, 0, length(deneme)) == 1);
	assert(count(string, 0, len) >= 1);
	
	Cum[0] := 0;
	i := 1;
	while (i < 256)
  invariant(i <= 256);
	invariant(Cum[0] == 0);
	invariant(forall k: int:: {Cum[k-1]} ((1 <= k) && (k < i)) ==> (Cum[k] == Cum[k-1] + count(string, k, len-1)));
	{
	  Cum[i] := Cum[i-1] + count(string, i, len-1);
		i := i + 1;
	}
	Tot := Cum[i - 1];

	assert(Cum[0] == 0);
	assert(forall k: int:: {Cum[k-1]} ((1 <= k) && (k < 256)) ==> ((Cum[k] - Cum[k-1]) == count(string, k, len-1)));
	assert(Tot == len);

	
  // ENCODING PART
	lo := 0;
	r0 := 1;

	r := 0;
	while (r == 0)
	{
	  lo := 0;
		r := r0;

		r_arr[-1] := r;
		lo_arr[-1] := lo;
		
		i := 0;
		while (i < len)
		invariant(i <= len);
		invariant((i > 0) ==> ((lo == lo_arr[i-1]) && (r == r_arr[i-1])));
		invariant(forall k: int :: {Cum[string[k]]} (0 <= k && k < i) ==> (r_arr[k] == (((r_arr[k-1] * Cum[string[k]]) / Tot) - ((r_arr[k-1] * Cum[string[k]-1]) / Tot))));  // TODO: without trigger hangs
		invariant(forall k: int :: {Cum[string[k]]} (0 <= k && k < i) ==> (lo_arr[k] == (lo_arr[k-1] + ((r_arr[k-1] * Cum[string[k]]) / Tot))));  // TODO: without trigger hangs
		{
		  c := string[i];
			
		  lo_arr[i] := lo + ((r * Cum[c-1]) / Tot);
			lo := lo_arr[i];

			r_arr[i] := ((r * Cum[c])/Tot) - ((r * Cum[c-1])/Tot);
			r := r_arr[i];
			
			i := i + 1;
		}

		r0 := r0 * 2;
	}


	// DECODING PART
	r := r0 / 2;
	x := lo;
	i := 0;
	while (i < len)
	invariant(i <= len);
	{
	  c := 0;

		while (((r*Cum[c]) / Tot) <= x)
		{
				c := c + 1;
		}
		
	  out[i] := c;
	  x := x - ((r * Cum[c-1]) / Tot);
		r := ((r * Cum[c]) / Tot) - ((r * Cum[c-1]) / Tot);
	  i := i + 1;
	}

	assert(i == len);
	out[i] := 0;
}

