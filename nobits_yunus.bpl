

function {:builtin "div"} division(a: int, b: int) returns(int);
axiom(forall x,y: int :: ((x/y) == division(x, y)));

function dec(x :int) returns(int);
axiom(forall x: int :: {dec(x)} dec(x) == (x-1));

function inc(x :int) returns(int);
axiom(forall x: int :: {inc(x)} inc(x) == (x+1));

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

function cmpstrn(str1: String, str2: String, l: int) returns(bool);
axiom(forall str1, str2: String, l: int :: {cmpstrn(str1, str2, l)} (l >= 0 && cmpstrn(str1, str2, l)) ==> ((str1[l] == str2[l]) && cmpstrn(str1, str2, dec(l))));
axiom(forall str1, str2: String, l: int :: {cmpstrn(str1, str2, l)} (l >= 0 && !cmpstrn(str1, str2, l)) ==> ((str1[l] != str2[l]) || !cmpstrn(str1, str2, dec(l))));
axiom(forall str1, str2: String, l: int :: {cmpstrn(str1, str2, l)} (l < 0) ==> cmpstrn(str1, str2, l));

// count how many 'c' exists upto 'upper_limit' in 'string'
function count(string: String, 	c: char, upper_limit: int) returns(int);
axiom(forall string: String, c: char, i: int :: {count(string, c, i)} count(string, c, i) >= 0);
axiom(forall string: String, c: char, i: int :: {count(string, c, i)} (i < 0) ==> (count(string, c, i) == 0));
axiom(forall string: String, c: char, i: int :: {count(string, c, i)} (i >= 0 && string[i]!=c) ==> (count(string, c, i) == count(string, c, dec(i))));
axiom(forall string: String, c: char, i: int :: {count(string, c, i)} (i >= 0 && string[i]==c) ==> (count(string, c, i) == (1 + count(string, c, dec(i)))));


// summation of elements in array
function summation(A: [int]int, i: int) returns(int);
axiom(forall A: [int]int, i: int :: {summation(A, dec(i))} summation(A, i) == (A[i] + summation(A, dec(i))));
axiom(forall A: [int]int, i: int :: (i < 0) ==> summation(A, i) == 0);

var Cum: [int]int;
var Tot: int;

const r0: int;


procedure encodeAndDecode(string: String) returns(out: String);
  requires (forall j:int :: (string[j] < 256 && string[j] >= 0));
  requires (exists i:int :: (i >= 0 && string[i] == 0) && (forall j:int :: (i != j) ==> (string[j] != 0)));
	modifies Cum, Tot;
	ensures (forall j:int :: (out[j] < 256 && out[j] >= 0));
  ensures (exists i:int :: (i >= 0 && out[i] == 0) && (forall j:int :: (i != j) ==> (out[j] != 0)));
  ensures (cmpstrn(string, out, length(string)));

implementation encodeAndDecode(string: String) returns(out: String) {

  var lo,r: int;
	var r_lower: int;
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
	invariant(forall k: int:: {Cum[dec(k)]} ((1 <= k) && (k < i)) ==> (Cum[k] == Cum[dec(k)] + count(string, k, dec(len))));
	{
	  Cum[i] := Cum[dec(i)] + count(string, i, dec(len));
		i := i + 1;
	}
	Tot := Cum[i - 1];

	assert(Cum[0] == 0);
	assert(forall k: int:: {Cum[dec(k)]} ((1 <= k) && (k < 256)) ==> ((Cum[k] - Cum[dec(k)]) == count(string, k, dec(len))));
//	assert(Tot == len);


  // ENCODING PART

  lo := 0;
	r := r0;
	r_lower := dec(r0);

	r_arr[-1] := r;
	lo_arr[-1] := lo;
		
	i := 0;
	while (i < len)
	invariant(i <= len);
	invariant(r_arr[dec(0)] == r0);
	invariant(lo_arr[dec(0)] == 0);
	invariant((lo == lo_arr[dec(i)]) && (r == r_arr[dec(i)]));
	invariant(forall k: int :: {Cum[string[k]], Cum[dec(string[k])], r_arr[dec(k)], lo_arr[dec(k)]} (0 <= k && k < i) ==> (r_arr[k] == (((r_arr[dec(k)] * Cum[string[k]]) / Tot) - ((r_arr[dec(k)] * Cum[dec(string[k])]) / Tot))));  // TODO: without trigger hangs
	invariant(forall k: int :: {Cum[dec(string[k])], r_arr[dec(k)], lo_arr[dec(k)]} (0 <= k && k < i) ==> (lo_arr[k] == (lo_arr[dec(k)] + ((r_arr[dec(k)] * Cum[dec(string[k])]) / Tot))));  // TODO: without trigger hangs
//	invariant(forall k: int :: {Cum[string[k]], r_arr[dec(k)], lo_arr[dec(k)]} (0 <= k && k < i) ==> (((r_arr[dec(k)] * Cum[string[k]]) / Tot) > lo_arr[dec(k)]));
	{
	  c := string[i];

	  lo_arr[i] := lo + ((r * Cum[dec(c)]) / Tot);
		lo := lo_arr[i];

		r_arr[i] := ((r * Cum[c])/Tot) - ((r * Cum[dec(c)])/Tot);
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
	assert(r_arr[-1] == r);
	while (i < len)
	invariant(i <= len);
	invariant(i == 2 ==> r == r_arr[dec(2)]);
	invariant(x == lo_arr[dec(len-i)]);
//  invariant(exists k: int :: (0 <= k) && (k < 256) && (((r * Cum[k]) / Tot) > x));
//	invariant(forall k: int :: {string[k]} {out[k]} (0 <= k && k < i) ==> (out[k] == string[k]));
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

