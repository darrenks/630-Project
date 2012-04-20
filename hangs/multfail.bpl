procedure CompressAndDecompress(in: [int]int, r0: int, counts: [int]int, nsyms: int, len: int) returns (out: [int]int)
    requires len>0;
    requires nsyms>0;
    requires (forall i: int :: i>=0 && i<len ==> in[i]>=0 && in[i]<nsyms);
    requires r0>0;
    //todo counts[in[i]]>0
    ensures (forall i: int :: i>=0 && i<len ==> in[i]==out[i]);
{
var lo, r, i, c, x : int;
var r1, r2 : [int]int; //auxiliary variables used to prove r is same
var tot: int;
var ps: [int]int;

// ps[0]:=0;
// i := 0;
// while (i<nsyms)
// invariant (forall j: int :: j>=0 && j<i ==> ps[j+1]==ps[j]+counts[j]);
// {
//     ps[i+1] := ps[i]+counts[i];
//     i := i+1;
// }
// tot := ps[nsyms];

//compress
lo := 0;
r := r0;

r1[0] := r;

i := 0;
while (i < len)
invariant i <= len;
invariant r1[0] == r0;
//invariant (forall j: int :: j>=0 && j<i ==>
//    r1[j+1] == r1[j]*ps[in[j]+1]/tot-r1[j]*ps[in[j]]/tot );
invariant (forall j: int :: j>=0 && j<i ==> r1[j+1] == r1[j]/ps[in[j]]);
{
    //c := in[i];
    
    lo := r1[i]*ps[in[i]]/tot;
//    r := r*ps[in[i]+1]/tot-r*ps[in[i]]/tot;
//   r1[i+1] := r1[i]*ps[in[i]+1]/tot-r1[i]*ps[in[i]]/tot;
    r1[i+1] := r1[i]/ps[in[i]];
    
//THIS LINE ^ FAILS with * but not with /
    
    assume r1[i]>0;
    
    i := i+1;
}

//decompress
x := lo;
r := r0;

r2[0] := r;

i := 0;
while (i < len)
invariant i<= len; //might be unneeded
invariant (forall j: int :: j>=0 && j<i ==> out[j]==in[j]);
//invariant (r == r1[i]);
{
    c := 0;
    while (r*ps[c+1]/tot<=x)
    invariant true;
    {
        c := c+1;
    }
    out[i] := c;
    assume (out[i] == in[i]); //TODO

    x := r*ps[c]/tot;
    r := r*ps[c+1]/tot-r*ps[c]/tot;
    //r2[i+1] := r2[i]*ps[in[i]+1]/tot-r2[i]*ps[in[i]]/tot;
    
    i := i+1;
}

} //end procedure