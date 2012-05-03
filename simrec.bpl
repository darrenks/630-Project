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
axiom (forall i,j,r: int :: i<j ==> get_lo_range(i, r) < get_lo_range(j, r));
axiom (forall r: int :: {get_lo_range(0, r)} r>0 ==> get_lo_range(0, r)==0);
axiom (forall r: int :: {get_lo_range(nsyms,r)} r>0 ==> get_lo_range(nsyms, r)==r);

axiom (forall i,r: int :: {get_lo_range(i,r)} get_lo_range(i, r)==i*r/nsyms);

procedure get_lo_rangep(sym: int, range: int) returns(lo: int)
requires sym>=0 && sym<=nsyms;
requires range>0;
ensures lo == get_lo_range(sym, range);
{
    lo := sym*range/nsyms;
}
function get_hi_range(sym: int, range: int) returns(int);
//axiom (forall i,r: int :: {get_hi_range(i,r)} get_hi_range(i,r)==r*(i+1)/nsyms);
axiom (forall i,r: int :: {get_hi_range(i,r)} get_hi_range(i,r)<=r && get_lo_range(i,r) < get_hi_range(i,r));
axiom (forall i,r: int :: {get_hi_range(i,r)} get_hi_range(i,r) == get_lo_range(i+1, r)); //<= works too

procedure get_hi_rangep(sym: int, range: int) returns(hi: int)
requires sym>=0 && sym<nsyms;
requires range>0;
ensures hi == get_hi_range(sym, range);
{
    call hi := get_lo_rangep(sym+1, range); //TODO
}

// function lookup(x: int, range: int) returns(int);
// //pre? x>=0 && x<r ==> 
// //axiom (forall x,r: int :: {lookup(x,r)} x>=get_lo_range(lookup(x,r), r) && x<get_hi_range(lookup(x,r), r));
// axiom (forall xx,r,y: int :: y==lookup(xx,r) <==> xx>=get_lo_range(y, r) && xx<get_hi_range(y, r));

procedure lookup(x: int, range: int) returns(y: int)
requires x>=0 && x<range;
ensures x>=get_lo_range(y, range) && x<get_hi_range(y, range);
ensures (forall yy: int :: yy != y ==> x<get_lo_range(yy, range) || x>=get_hi_range(yy, range));
{
    var hi: int;
    y := 0;
    while (true)
    invariant x>=get_lo_range(y, range);
    invariant y<nsyms;
    {
        call hi := get_hi_rangep(y, range);
        if (hi>x) { break; }
        y := y+1;
    }
    //these help it run faster
    assert (forall yy: int :: yy > y ==> x<get_lo_range(yy, range));
    assert (forall yy: int :: yy < y ==> x>=get_hi_range(yy, range));
}

function encodef(ind: int, range: int) returns (int);
axiom (forall i,r: int :: {encodef(i, r)} i>=len ==> encodef(i, r) == 0);
axiom (forall i,r: int :: {encodef(i, r)} i>=0 && i<len ==> encodef(i, r) == get_lo_range(in[i], r)+encodef(i+1, get_hi_range(in[i], r)-get_lo_range(in[i], r)));

//TODO
axiom (forall i,r: int :: {encodef(i, r)} i>=0 && i<len ==> encodef(i, r) >= get_lo_range(in[i], r) && encodef(i, r) < get_hi_range(in[i], r));

procedure encode(ind: int, range: int) returns (x: int)
    requires len>=0;
    requires ind>=0 && ind<=len;
    requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
    //requires range>0;
    ensures x>=0 && x<range;
    ensures ind>=len ==> x==0;
    ensures ind<len ==> x>=get_lo_range(in[ind], range) && x<get_hi_range(in[ind], range);
    //ensures x in the range that makes out[i]==in[i], recursive call
    ensures x == encodef(ind, range);
{
    var c, lo, hi: int;
    assume (range > 0); // TODO
    if (ind>=len) { x:= 0; return; }
    c := in[ind];
    call lo := get_lo_rangep(c, range);
    call hi := get_hi_rangep(c, range);
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
    ensures ((x==encodef(ind, range)) ==> (forall i: int :: i>=ind && i<len ==> out[i]==in[i]));
    //ensures x==encodef(ind, range) && ind<len ==> out[ind]==in[ind];
{
    var c, lo, hi: int;
    assume (range > 0); // TODO
    if (ind>=len) { return; }
    call c := lookup(x, range);
    
    assume(c>=0 && c<=nsyms); //TODO
    call lo := get_lo_rangep(c, range); assert(lo == get_lo_range(c, range));
    hi := get_hi_range(c, range);
    //assume (x>=lo); // TODO
    call decode(ind+1, hi-lo, x-lo);
    out[ind] := c;
}

procedure main() modifies out; {
    var x: int;
    var range: int where range>0; //TODO calc range
       
    call x := encode(0, range);
    
    //assume(x >= 0 && x<range);
    
    call decode(0, range, x);
    assert (forall i: int :: i>=0 && i<len ==> out[i]==in[i]);
}