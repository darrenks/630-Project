
type char = int;
type String = [int]int;

const string: String;
const len: int;
const Cum: [char]int;
const r0: int;

axiom(len > 0);


function get_range(r: int, c: char, cum: [char]int) returns(int);
axiom(forall r: int, c: char, cum: [char]int :: get_range(r, c, cum) >= 0 && get_range(r, c, cum) <= r);

function get_upper_bound(low: int, r: int, c: char, cum: [char]int) returns(int);
axiom(forall low, r: int, c: char, cum: [char]int :: get_upper_bound(low, r, c, cum) ==
                                                     get_lower_bound(low, r, c, cum) + get_range(r, c, cum));

function get_lower_bound(low: int, r: int, c: char, cum: [char]int) returns(int);
axiom(forall low, r: int, c: char, cum: [char]int :: low <= get_lower_bound(low, r, c, cum));
axiom(forall low, r: int, c: char, cum: [char]int ::
                                          get_lower_bound(low, r, c, cum) <= get_upper_bound(low, r, c, cum));
axiom(forall low, r: int, c: char, cum: [char]int :: get_upper_bound(low, r, c, cum) <= low + r);

function exists?(r: int, c: char, cum: [char]int) returns(bool);
axiom(forall r: int, c: char, cum: [char]int :: exists?(r, c, cum) <==> get_range(r, c, cum) > 0);
axiom(forall r: int, c: char, cum: [char]int :: exists?(r, c, cum) <==> (exists i: int :: string[i] == c));

axiom(forall low, r: int, c1,c2: char, cum: [char]int :: (c1 != c2) <==>
                                      ((get_upper_bound(low, r, c1, cum) <= get_lower_bound(low, r, c2, cum)) ||
																		   (get_upper_bound(low, r, c2, cum) <= get_lower_bound(low, r, c1, cum))));

function int2char(low: int, r: int, cum: [char]int, x: int) returns(char);
axiom(forall low, r: int, cum: [char]int, x: int :: (r >= 0 && x >= low && x <= low + r) ==>
                                           (exists c: char :: (int2char(low, r, cum, x) == c) &&
																					 ((get_lower_bound(low, r, c, cum) <= x) &&
																					  (x < get_upper_bound(low, r, c, cum)))));


						 
procedure encodeAndDecode();
  ensures(forall low, r: int, c: char, cum: [char]int :: exists?(r, c, cum) <==>
                                            (get_lower_bound(low, r, c, cum) < get_upper_bound(low, r, c, cum)));


implementation encodeAndDecode() {
  var i: int;
	var c: char;
	var r: int;
	var x: int;
	var low: int;
	var out: String;
	var low_arr: [int]int;
	var r_arr: [int]int;

	i := 0;
	low := 0;
	r := r0;

	r_arr[-1] := r;
	low_arr[-1] := low;
	
	assume(r > 0);
  while(i < len)
	invariant(i <= len);
	invariant(low >= 0);
	invariant(r >= 0);
	invariant(r <= r0);
	invariant(r_arr[-1] == r0);
	invariant(low_arr[-1] == 0);
	invariant(r == r_arr[i-1]);
	invariant(low == low_arr[i-1]);
	invariant((i > 0 && i <= len) ==> c == string[i-1]);
	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[k] == get_lower_bound(low_arr[k-1], r_arr[k-1], string[k], Cum));
	invariant(forall k: int :: (0 <= k && k < i) ==> r_arr[k] == get_range(r_arr[k-1], string[k], Cum));
//	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[k] >= low_arr[k-1]);
//	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[k-1] + r_arr[k-1] >= low_arr[k] + r_arr[k]);
//	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[k] < low_arr[k-1] + r_arr[k-1]);
	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[k] <= low_arr[i-1]);                             // If you comment out this three, you wouldn't get the proof. Try it out.
	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[k] + r_arr[k] >= low_arr[i-1] + r_arr[i-1]);
	invariant(forall k: int :: (0 <= k && k < i) ==> low_arr[i-1] < low_arr[k] + r_arr[k]);
//	invariant(forall k,m: int :: (0 <= k && k <= m && m < i) ==> low_arr[k] <= low_arr[m]);
//	invariant(forall k,m: int :: (0 <= k && k <= m && m < i) ==> low_arr[k] + r_arr[k] >= low_arr[m] + r_arr[m]);
//	invariant(forall k,m: int :: (0 <= k && k <= m && m < i) ==> low_arr[m] < low_arr[k] + r_arr[k]);
	{
	  c := string[i];
		
    low_arr[i] := get_lower_bound(low, r, c, Cum);
		low := low_arr[i];
		
    r_arr[i] := get_range(r, c, Cum);
		r := r_arr[i];
		
		i := i + 1;
	}

	x := low;

	assert(low == low_arr[len-1]);
  assert(low_arr[len-1] <= low_arr[len-2] + r_arr[len-2]);
	
  low := 0;
	r := r0;
	i := 0;

	assert(x == low_arr[len - 1]);
	assert(x <= low_arr[0] + r_arr[0]);
	
	while(i < len)
	invariant(i <= len);
	invariant(low >= 0);
	invariant(r >= 0);
	invariant(r <= r0);
	invariant(low == low_arr[i-1]);
  invariant(r == r_arr[i-1]);
	invariant(i > 0 ==> out[i-1] == string[i-1]);
	{
    c := int2char(low, r, Cum, x);
		out[i] := c;

		low := get_lower_bound(low, r, c, Cum);
		
    r := get_range(r, c, Cum);
		
    i := i + 1;
	}
	// TODO: a recursive function needed to complete full comparison of strings.

}

