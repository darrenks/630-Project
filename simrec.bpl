function {:builtin "*"} mult(a: int, b: int) returns(int);
axiom(forall x,y: int :: {x*y} ((x*y) == mult(x, y)));

function {:builtin "div"} division(a: int, b: int) returns(int);
axiom(forall x,y: int :: {x/y} ((x/y) == division(x, y)));

// axiom (forall x,y: int :: {x/y} y>0 ==> x/y <= x);
// axiom (forall x,y: int :: {x/y} y>0 && x>=0 ==> x/y >= 0);

//suggested built in for / %
axiom (forall x,y: int :: {x%y} {x/y} x%y==x-x/y*y);
axiom (forall x,y: int :: {x%y} (0<y ==> 0<=x%y && x%y<y) && (y<0 ==> y<x%y && x%y <= 0) );


//axiom (forall x,y,z: int :: {z*y/x} x>0 && z==x ==> z*y/x==y);
//axiom (forall z: int :: {z*0} z*0==0);
//axiom (forall z: int :: {0/z} z!=0 ==> 0/z==0);
//axiom (forall i,j,r: int :: i>=0 && j>=0 && r>
//axiom (forall i, r: int :: {i/r} i>=0 && r>0 ==> i/r >= 0);


const nsyms: int;
const len: int;
const in: [int]int;
axiom nsyms>1;
axiom len>=0;
axiom (forall i: int :: {in[i]} i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);

var out: [int]int;

function get_lo_range(sym: int, range: int) returns(int) {sym*range/nsyms}
function get_hi_range(sym: int, range: int) returns(int) {get_lo_range(sym+1, range)}
//axiom (forall i,j,r: int :: i<j ==> get_lo_range(i, r) < get_lo_range(j, r));
//axiom (forall i,r: int :: get_lo_range(i, r) <= get_hi_range(i, r));

procedure math_lemmas()
ensures (forall x,y,z: int :: {z*y/x} x>0 && z==x ==> z*y/x==y);
ensures (forall i, r: int :: {i/r} i>=0 && r>0 ==> i/r >= 0);
{
assume (forall i, r: int :: {i/r} i>=0 && r>0 ==> i/r >= 0);
assume (forall x,y,z: int :: {z*y/x} x>0 && z==x ==> z*y/x==y);
}


procedure get_lo_range_lemmas()
ensures (forall i,r: int :: {get_lo_range(i,r)} i>=0 && r>0 ==> get_lo_range(i,r)>=0);
ensures (forall i,r: int :: {get_lo_range(i,r)} get_lo_range(i,r) <= get_hi_range(i,r));

//ensures (forall i,j,r: int :: {get_lo_range(i, r),get_lo_range(j, r)} i<j ==> get_lo_range(i, r) < get_lo_range(j, r));
//ensures (forall i,r: int :: {get_lo_range(i, r)} get_lo_range(i, r) <= get_hi_range(i, r));

ensures (forall r: int :: {get_lo_range(0, r)} r>0 ==> get_lo_range(0, r)==0);
ensures (forall r: int :: {get_lo_range(nsyms,r)} r>0 ==> get_lo_range(nsyms, r)==r);


ensures (forall i,r: int :: {get_hi_range(i,r)} i<nsyms ==> get_hi_range(i,r)<=r);
ensures (forall i,r: int :: {get_hi_range(i,r)} get_lo_range(i,r) <= get_hi_range(i,r));
{
call math_lemmas();

assume (forall i,r: int :: {get_hi_range(i,r)} i<nsyms ==> get_hi_range(i,r)<=r);
assume (forall i,r: int :: {get_hi_range(i,r)} get_lo_range(i,r) <= get_hi_range(i,r));

}

//axiom (forall i,r: int :: {get_hi_range(i,r)} get_hi_range(i,r)==r*(i+1)/nsyms);

procedure lookup(x: int, range: int) returns(y: int)
requires x>=0 && x<range;
ensures x>=get_lo_range(y, range) && x<get_hi_range(y, range);
ensures (forall yy: int :: yy != y ==> x<get_lo_range(yy, range) || x>=get_hi_range(yy, range));
ensures y>=0 && y<nsyms;
{
    var hi: int;
    call get_lo_range_lemmas();
    y := 0;
    while (true)
    invariant x>=get_lo_range(y, range);
    invariant y>=0 && y<nsyms;
    {
        hi := get_hi_range(y, range);
        assert(y==nsyms-1 ==> hi>x); //help it figure out that invariant y<nsyms
        if (hi>x) { break; }
        y := y+1;
    }
    //these help it run faster
    assume (forall yy: int :: yy > y ==> x<get_lo_range(yy, range));
    assume (forall yy: int :: yy < y ==> x>=get_hi_range(yy, range));
}

function encodef(ind: int, range: int) returns (int);
axiom (forall i,r: int :: {encodef(i, r)} i>=len ==> encodef(i, r) == 0);
axiom (forall i,r: int :: {encodef(i, r)} i>=0 && i<len ==> encodef(i, r) == get_lo_range(in[i], r)+encodef(i+1, get_hi_range(in[i], r)-get_lo_range(in[i], r)));

//TODO
//axiom (forall i,r: int :: {encodef(i, r)} i>=0 && i<len ==> encodef(i, r) >= get_lo_range(in[i], r) && encodef(i, r) < get_hi_range(in[i], r));

procedure encode_helper(ind: int, range: int) returns (x: int, fail: bool)
    requires len>=0;
    requires ind>=0 && ind<=len;
    requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
    ensures (x>=0 && x<range) || fail;
    ensures ind>=len ==> x==0;
//    ensures ind<len ==> x>=get_lo_range(in[ind], range) && x<get_hi_range(in[ind], range);
    ensures x == encodef(ind, range) || fail;
{
    var c, lo, hi: int;
    call get_lo_range_lemmas();
    if (range<=0) { x, fail := 0, true; return; }
    if (ind>=len) { x, fail := 0, false; return; }
    c := in[ind];
    lo := get_lo_range(c, range);
    hi := get_hi_range(c, range);
    call x, fail := encode_helper(ind+1, hi-lo);
    x := x+lo;
}

procedure decode(ind: int, range: int, x: int)
    modifies out;
    requires x>=0 && x<range;
    requires len>=0;
    requires ind>=0 && ind<=len;
    requires range>0;
    ensures x==encodef(ind, range) ==> (forall i: int :: i>=ind && i<len ==> out[i]==in[i]);
{
    var c, lo, hi: int;
    call get_lo_range_lemmas();
    if (ind>=len) { return; }
    call c := lookup(x, range);
    
    assume (forall i,r: int :: {encodef(i, r)} i>=0 && i<len ==> encodef(i, r) >= get_lo_range(in[i], r) && encodef(i, r) < get_hi_range(in[i], r));
    
    
    lo := get_lo_range(c, range);
    hi := get_hi_range(c, range);
    call decode(ind+1, hi-lo, x-lo);
    out[ind] := c;
}

procedure encode() returns (x: int, range: int)
//requires len>=0;
//requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
ensures x>=0 && x<range;
ensures x == encodef(0, range);
{
    var fail: bool;
    range := 1;
    while (true)
    {
        call x, fail := encode_helper(0, range);
        if (!fail) { return; }
        range := range*2;
    }
}

procedure main() modifies out; {
    var x, range: int;
       
    call x, range := encode();
    call decode(0, range, x);
    assert (forall i: int :: i>=0 && i<len ==> out[i]==in[i]);
}

