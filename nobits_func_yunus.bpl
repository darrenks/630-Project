

type char = int;
type String = [int]int;

const string: String;
const len: int;
const Cum: [char]int;

axiom(len > 0);

function get_lower_bound(r: int, c: char, cum: [char]int) returns(int);
function get_upper_bound(r: int, c: char, cum: [char]int) returns(int);
axiom(forall r: int, c: char, cum: [char]int :: (r >= 0) ==> 0 <= get_lower_bound(r, c, cum));
axiom(forall r: int, c: char, cum: [char]int :: (r >= 0) ==> get_lower_bound(r, c, cum) <= get_upper_bound(r, c, cum));
axiom(forall r: int, c: char, cum: [char]int :: (r >= 0) ==> get_upper_bound(r, c, cum) <= r);

function exists?(r: int, c: char, cum: [char]int) returns(bool);
axiom(forall r: int, c: char, cum: [char]int :: exists?(r, c, cum) <==>
                                                (get_lower_bound(r, c, cum) < get_upper_bound(r, c, cum)));
axiom(forall r: int, c: char, cum: [char]int :: exists?(r, c, cum) <==> (exists i: int :: string[i] == c));

axiom(forall r: int, c1,c2: char, cum: [char]int :: (c1 != c2) ==>
                                      ((get_upper_bound(r, c1, cum) <= get_lower_bound(r, c2, cum)) ||
																		   (get_upper_bound(r, c2, cum) <= get_lower_bound(r, c1, cum))));

function char2range(r: int, c: char, cum: [char]int) returns(int);
axiom(forall r: int, c: char, cum: [char]int :: exists?(r, c, cum) ==>
            (get_lower_bound(r, c, cum) <= char2range(r, c, cum) &&
						 char2range(r, c, cum) < get_upper_bound(r, c, cum)));

axiom(forall r: int, c1,c2: char, cum: [char]int :: (c1 == c2) <==>
            (get_lower_bound(r, c1, cum) <= char2range(r, c2, cum) &&
						 char2range(r, c2, cum) < get_upper_bound(r, c1, cum)));

function int2char(r: int, cum: [char]int, x: int) returns(char);
axiom(forall r: int, cum: [char]int, x: int :: (r >= 0 && x >= 0) ==> (exists c: char :: (int2char(r, cum, x) == c) && ((get_lower_bound(r, c, cum) <= x) && (x < get_upper_bound(r, c, cum)))));

const r0: int;
						 
procedure encodeAndDecode();

implementation encodeAndDecode() {
  var i: int;
	var c: char;
	var r: int;
	var x: int;
	var low: int;
	var out: String;
	var old_r: int;
	var old_low: int;

	i := 0;
	low := 0;
	r := r0;
	assume(r > 0);
  while(i < len)
	invariant(i <= len);
	invariant(r > 0);
	invariant(low >= 0);
	{
	  c := string[i];
		old_low := low;
		low := low + get_lower_bound(r, c, Cum);
		old_r := r;
    r := get_upper_bound(r, c, Cum) - get_lower_bound(r, c, Cum);
		assert((old_low <= low) && (old_low + old_r >= low + r));
		i := i + 1;
	}

	
	r := r0;
	x := low;
	i := 0;

	while(i < len)
	invariant(i <= len);
	invariant(forall k: int :: (0 <= k && k < i) ==> (out[k] == string[k]));
	{
	  c := int2char(r, Cum, x);
		out[i] := c;
		x := x - get_lower_bound(r, c, Cum);
		r := get_upper_bound(r, c, Cum) - get_lower_bound(r, c, Cum);
    i := i + 1;
	}

	assert(out[0] == string[0]);
}

