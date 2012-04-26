function {:builtin "*"} mult(a: int, b: int) returns(int);
//axiom(forall x,y: int :: {x*y} ((x*y) == mult(x, y)));

function {:builtin "div"} division(a: int, b: int) returns(int);
//axiom(forall x,y: int :: {x/y} ((x/y) == division(x, y)));
// axiom (forall x,y: int :: {x/y} y>0 ==> x/y <= x);
// axiom (forall x,y: int :: {x/y} y>0 && x>=0 ==> x/y >= 0);

const nsyms: int;
const len: int;
const in: [int]int;
axiom nsyms>1;
axiom len>=0;
axiom (forall i: int :: {in[i]} i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);

var out: [int]int;

function get_lo_range(sym: int, range: int) returns(int);
//axiom (forall i,r: int :: {get_lo_range(i,r)} get_lo_range(i,r)==r*i/nsyms);
axiom (forall i,r: int :: {get_lo_range(i,r)} get_lo_range(i,r)>=0 && get_lo_range(i,r) < get_hi_range(i,r));

function get_hi_range(sym: int, range: int) returns(int);
//axiom (forall i,r: int :: {get_hi_range(i,r)} get_hi_range(i,r)==r*(i+1)/nsyms);
axiom (forall i,r: int :: {get_hi_range(i,r)} get_hi_range(i,r)<=r && get_lo_range(i,r) < get_hi_range(i,r));

function lookup(x: int, range: int) returns(int);
axiom (forall x,r: int :: {lookup(x,r)} x>=0 && x<r ==> x<=get_lo_range(lookup(x,r), r) && x<get_hi_range(lookup(x,r), r));


procedure encode(ind: int, range: int) returns (x: int)
    requires len>=0;
    requires ind>=0 && ind<=len;
    requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
    //requires range>0;
    ensures x>=0 && x<range;
    ensures ind<len ==> x>=get_lo_range(in[ind], range) && x<get_hi_range(in[ind], range);
    //ensures x in the range that makes out[i]==in[i], recursive call
{
    var c, lo, hi: int;
    assume (range > 0); // TODO
    if (ind>=len) { x:= 0; return; }
    c := in[ind];
    lo := get_lo_range(c, range);
    hi := get_hi_range(c, range);
    call x := encode(ind+1, hi-lo);
    
    x := x+lo;
}

procedure decode(ind: int, range: int, x: int)
    modifies out;
    requires x>=0 && x<range;
    requires len>=0;
    requires ind>=0 && ind<=len;
    requires range>0;
//    ensures that gets first letter right and returns decode(1..)
    ensures (forall i: int :: i>=ind && i<len ==> out[i]==in[i]);
{
    var c, lo, hi: int;
    assume (range > 0); // TODO
    if (ind>=len) { return; }
    c := lookup(x, range);
    assume (c == in[ind]); //TODO this is cheating
    lo := get_lo_range(c, range);
    hi := get_hi_range(c, range);
    assume (x>=lo); // TODO
    call decode(ind+1, hi-lo, x-lo);
    out[ind] := c;
}

procedure main() modifies out; {
    var x: int;
    var range: int where range>0; //TODO calc range
       
    call x := encode(0, range);
    call decode(0, range, x);
    assert (forall i: int :: i>=0 && i<len ==> out[i]==in[i]);
}