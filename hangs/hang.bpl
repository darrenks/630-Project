procedure CompressAndDecompress(in: [int]int, r0: int, counts: [int]int, nsyms: int, len: int) returns (out: [int]int)
    requires len>0;
    requires nsyms>0;
    requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
    requires r0>0;
    //requires each symbol non 0 probability
//    ensures (forall i: int :: i>=0 && i<len ==> in[i]==out[i]);
{
var i : int;
var r1 : [int]int; //auxiliary variables used to prove r is same

var ps : [int]int;
ps[0]:=0;
i := 0;
while (i<nsyms)
invariant (forall j: int :: j>=0 && j<i ==> ps[j+1]==ps[j]+counts[j]);
{
    ps[i+1] := ps[i]+counts[i];
    i := i+1;
}

//axiom (forall i: int :: i>=0 && i<256 ==> ps[i+1]==ps[i]+counts[i]);


//compress
r1[0] := r0;

i := 0;
while (i < len)
invariant i <= len;
invariant (forall j: int :: j>=0 && j<i ==> r1[j+1] == r1[j]+1);
{
    r1[i+1] := r1[i]+1;
        
    i := i+1;
}

//decompress

i := 0;
while (i < len)
invariant i<= len; //might be unneeded
invariant (forall j: int :: j>=0 && j<i ==> out[j]==in[j]);
{
    out[i] := in[i];
//    assume (out[i] == in[i]); //TODO
    
    i := i+1;
}

} //end procedure