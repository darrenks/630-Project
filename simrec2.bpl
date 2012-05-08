const nsyms: int;
const len: int;
const in: [int]int;
axiom nsyms>2;
axiom len>=0;
axiom (forall i: int :: {in[i]} i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);

var out: [int]int;

function lo_range(sym: int, range: int) returns(int);
function hi_range(sym: int, range: int) returns(int) { lo_range(sym+1, range) }

procedure range_bound_lemma()
ensures (forall r: int :: {lo_range(0, r)} lo_range(0, r) == 0);
ensures (forall c, r: int :: c>=0 && c<nsyms && r>0 ==> lo_range(c, r) >= 0);
ensures (forall c, r: int :: c>=0 && c<nsyms && r>0 ==> hi_range(c, r) <= r);
ensures (forall r: int :: {hi_range(nsyms-1, r)} hi_range(nsyms-1, r) == r);
{
    assume (forall c, r: int :: c>=0 && c<nsyms && r>0 ==> lo_range(c, r) >= 0);
    assume (forall c, r: int :: c>=0 && c<nsyms && r>0 ==> hi_range(c, r) < r);
    assume (forall r: int :: {lo_range(0, r)} lo_range(0, r) == 0);
    assume (forall r: int :: {hi_range(nsyms-1, r)} hi_range(nsyms-1, r) == r);
}

procedure range_order_lemma()
ensures (forall i,j,r: int :: {lo_range(i,r),lo_range(j,r)} i<=j ==> lo_range(i,r) <= lo_range(j,r));
{
    assume (forall i,j,r: int :: {lo_range(i,r),lo_range(j,r)} i<=j ==> lo_range(i,r) <= lo_range(j,r));
}

procedure lookup(x: int, range: int) returns(y: int)
requires x>=0 && x<range;
ensures x>=lo_range(y, range) && x<hi_range(y, range);
ensures (forall yy: int :: yy != y ==> x<lo_range(yy, range) || x>=hi_range(yy, range));
{
    var hi: int;
    //assume(range>0);
    call range_bound_lemma();
    call range_order_lemma();
    y := 0;
    while (true)
    invariant x>=lo_range(y, range);
    invariant y>=0 && y<nsyms;
    {
        hi := hi_range(y, range);
        assert(y==nsyms-1 ==> hi>x); //help it figure out that invariant y<nsyms
        if (hi>x) { break; }
        y := y+1;
    }
    //these help it run faster
    //assert (forall yy: int :: yy > y ==> x<lo_range(yy, range));
    //assert (forall yy: int :: yy < y ==> x>=hi_range(yy, range));
}

function encodef(ind: int, range: int) returns (int);
axiom (forall i,r: int :: {encodef(i, r)} i>=len ==> encodef(i, r) == 0);
axiom (forall i,r: int :: {encodef(i, r)} i>=0 && i<len ==> encodef(i, r) == lo_range(in[i], r)+encodef(i+1, hi_range(in[i], r)-lo_range(in[i], r)));

//todo
//axiom (forall i,r: int :: {encodef(i, r)} r>0 ==> encodef(i, r)>=0 && encodef(i, r)<r);
procedure encodef_bound_lemma()
ensures (forall i,r: int :: {encodef(i, r)} r>0 ==> encodef(i, r)>=lo_range(in[i], r));
ensures (forall i,r: int :: {encodef(i, r)} r>0 ==> encodef(i, r)<hi_range(in[i], r));
{
    assume (forall i,r: int :: {encodef(i, r)} r>0 ==> encodef(i, r)>=lo_range(in[i], r));
    assume (forall i,r: int :: {encodef(i, r)} r>0 ==> encodef(i, r)<hi_range(in[i], r));
}

procedure encode_helper(ind: int, range: int) returns (x: int, fail: bool)
requires len>=0;
requires ind>=0 && ind<=len;
requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
ensures (x>=0 && x<range) || fail;
ensures ind>=len ==> x==0;
ensures x == encodef(ind, range) || fail;
{
    var c, lo, hi: int;
    call range_bound_lemma();
    if (range<=0) { x, fail := 0, true; return; }
    if (ind>=len) { x, fail := 0, false; return; }
    c := in[ind];
    lo := lo_range(c, range);
    hi := hi_range(c, range);
    call x, fail := encode_helper(ind+1, hi-lo);
    x := x+lo;
}

procedure decode_helper(ind: int, range: int, x: int)
modifies out;
requires x>=0 && x<range;
requires len>=0;
requires ind>=0 && ind<=len;
requires range>0;
ensures x==encodef(ind, range) ==> (forall i: int :: i>=ind && i<len ==> out[i]==in[i]);
//    requires x==encodef(ind, range);
//    ensures (forall i: int :: i>=ind && i<len ==> out[i]==in[i]) || fail;
{
    var c, lo, hi: int;
    call encodef_bound_lemma();
    if (ind>=len) { return; }
    call c := lookup(x, range);
    //assert (c==in[ind]);
    lo := lo_range(c, range);
    hi := hi_range(c, range);
    call decode_helper(ind+1, hi-lo, x-lo);
    out[ind] := c;
}

procedure encode() returns (x: int, range: int);
ensures x>=0 && x<range;
ensures x == encodef(0, range);
implementation encode() returns (x: int, range: int)
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

procedure decode(x: int, range: int)
modifies out;
requires x>=0 && x<range;
requires len>=0;
requires range>0;
ensures x==encodef(0, range) ==> (forall i: int :: i>=0 && i<len ==> out[i]==in[i]);
//requires x==encodef(0, range);
//ensures (forall i: int :: i>=0 && i<len ==> out[i]==in[i]);
{
    call decode_helper(0, range, x);
}

procedure main() modifies out; {
    var x, range: int;
       
    call x, range := encode();
    call decode(x, range);
    assert (forall i: int :: i>=0 && i<len ==> out[i]==in[i]);
}

