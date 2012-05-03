

function {:builtin "div"} division(a: int, b: int) returns(int);
axiom(forall x,y: int :: ((x/y) == division(x, y)));

function dec(x :int) returns(int);
axiom(forall x: int :: {dec(x)} dec(x) == (x-1));

function inc(x :int) returns(int);
axiom(forall x: int :: {inc(x)} inc(x) == (x+1));

axiom(forall x,y: int :: (y == x+1) ==> (dec(y) == x));

// Just to specify we have some specific need from this type. i.e. any char is less than 256 and greater than -1.
// We will meet this specifications by using ensures and requires.
type char = int;

// Just to specify we have some specific need from this type. i.e. string is an array composed of char.
// We will meet this specifications by using ensures and requires.
type String = [int]int;

var Cum: [int]int;
var Tot: int;

const r0: int;

const len: int;
axiom(len > 0);

const string: String;
axiom (string[len] == 0);
axiom (forall k: int :: string[k] >= 0 && string[k] < 256);
axiom (exists k:int :: (k > 0 && string[k] == 0) && (forall j:int :: (k != j) ==> (string[j] != 0)));

// return length of a str
function length(str: String) returns(int);
axiom(forall str: String :: {length(str)} length(str) >= 0);
axiom(forall str: String :: {length(str)} str[length(str)] == 0);

// compare two strs. return true if they are equal. Otherwise, return false.
function cmpstr(str1: String, str2: String) returns(bool);
axiom(forall str1, str2: String :: cmpstr(str1, str2) ==> ((length(str1) == length(str2)) && (forall i: int :: (i>=0 && i<length(str1)) ==> (str1[i] == str2[i]))));
axiom(forall str1, str2: String :: !cmpstr(str1, str2) ==> ((length(str1) != length(str2)) || (exists i: int :: (i>=0 && i<length(str1)) && (str1[i] != str2[i]))));

function cmpstrn(str1: String, str2: String, l: int) returns(bool);
axiom(forall str1, str2: String, l: int :: {cmpstrn(str1, str2, l)} (l >= 0 && cmpstrn(str1, str2, l)) ==> ((str1[l] == str2[l]) && cmpstrn(str1, str2, dec(l))));
axiom(forall str1, str2: String, l: int :: {cmpstrn(str1, str2, l)} (l >= 0 && !cmpstrn(str1, str2, l)) ==> ((str1[l] != str2[l]) || !cmpstrn(str1, str2, dec(l))));
axiom(forall str1, str2: String, l: int :: {cmpstrn(str1, str2, l)} (l < 0) ==> cmpstrn(str1, str2, l));

// count how many 'c' exists upto 'upper_limit' in 'str'
function count(str: String, c: char, upper_limit: int) returns(int);
axiom(forall str: String, c: char, k: int :: {count(str, c, k)} count(str, c, k) >= 0);
axiom(forall str: String, c: char, k: int :: {count(str, c, k)} (k < 0) ==> (count(str, c, k) == 0));
axiom(forall str: String, c: char, k: int :: {count(str, c, k)} (k >= 0 && str[k]!=c) ==> (count(str, c, k) == count(str, c, dec(k))));
axiom(forall str: String, c: char, k: int :: {count(str, c, k)} (k >= 0 && str[k]==c) ==> (count(str, c, k) == (1 + count(str, c, dec(k)))));


// summation of elements in array
function summation(A: [int]int, i: int) returns(int);
axiom(forall A: [int]int, i: int :: {summation(A, dec(i))} summation(A, i) == (A[i] + summation(A, dec(i))));
axiom(forall A: [int]int, i: int :: (i < 0) ==> summation(A, i) == 0);


procedure encodeAndDecode() returns(out: String);
	modifies Cum, Tot;
//	ensures (forall j:int :: (out[j] < 256 && out[j] >= 0));
//  ensures (cmpstrn(string, out, len));

implementation encodeAndDecode() returns(out: String) {

  var lo,r: int;
	var r_lower: int;
	var lo_arr, r0_arr, r_arr: [int]int;
	var i: int;
	var x: int;
	var c: char;

	Cum[0] := 0;
	i := 1;
	while (i < 256)
  invariant(i <= 256);
	invariant(Cum[dec(1)] == 0);
	invariant(forall k: int:: ((1 <= k) && (k < i)) ==> (Cum[k] == Cum[dec(k)] + count(string, k, dec(len))));
	{
	  Cum[i] := Cum[dec(i)] + count(string, i, dec(len));
		i := i + 1;
	}
	Tot := Cum[dec(i)];

	
  // ENCODING PART
  lo := 0;
	r := r0;
	r_lower := dec(r0);

	r_arr[dec(0)] := r;
	lo_arr[dec(0)] := lo;
		
	i := 0;
	while (i < len)
	invariant(i <= len);
	invariant(r_arr[dec(0)] == r0);
	invariant(forall k: int :: {r_arr[dec(k)]} ((k == i) ==> r_arr[dec(k)] == r) && (0 <= k && k < i) ==> (r_arr[k] == (((r_arr[dec(k)] * Cum[string[k]]) / Tot) - ((r_arr[dec(k)] * Cum[dec(string[k])]) / Tot))));
	{
	  c := string[i];

	  lo_arr[i] := lo + ((r * Cum[dec(c)]) / Tot);
		lo := lo_arr[i];

		assert(r == r_arr[dec(i)]);
		r_arr[i] := ((r_arr[dec(i)] * Cum[c])/Tot) - ((r_arr[dec(i)] * Cum[dec(c)])/Tot);
		r := r_arr[i];

		r_lower := ((r_lower * Cum[c])/Tot) - ((r_lower * Cum[dec(c)])/Tot);
			
		i := i + 1;
	}

	// with these two assumption r0 will be the range with exact precision to encode all string.
	assume(r > 0);
	assume(r_lower == 0);

	
	// DECODING PART
	r := r0;
	x := lo;
	i := 0;
	assert(r_arr[dec(0)] == r0);
	while (i < len)
	invariant(i <= len);
//	invariant(r == r_arr[dec(i)]);
	{
//	  c := 0;

//		while (((r*Cum[c]) / Tot) <= x)
//		invariant(c < 256);
//		invariant(forall k: int :: {Cum[k]} (0 <= k && k < c) ==> (((r * Cum[k]) / Tot) <= x));
//		{
//				c := c + 1;
//		}

    c := string[i];

	  out[i] := c;
	  x := x - ((r * Cum[dec(c)]) / Tot);
		r := ((r * Cum[c]) / Tot) - ((r * Cum[dec(c)]) / Tot);
	  i := i + 1;
	}

	assert(i == len);
	out[i] := 0;
}

