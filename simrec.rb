TestString='this is a test string, how well does it compress'
Len=TestString.size
OutString=' '*Len
counts=256.times.map{|i|TestString.count(i.chr)}
s=0; PS=[0]+counts.map{|i|s+=i}
Tot = PS[256]

def lo_hi(c, r)
    [r*PS[c]/Tot, r*PS[c+1]/Tot]
end

def encode(r, ind)
#requires forall i, counts[string[i]>0]
#requires ind>=0 and ind <= Len
#ensures that if decode(returned value, r, ind) is ran then forall i>=ind TestString[i]==OutString[i]
#TODO for now just assume r will not be 0, later we can algorithmically calculate initial r size so that it is always > 0
    return 0 if ind>=Len #empty string
    
    lo, hi = lo_hi(TestString[ind], r)
    
    lo + encode(hi-lo, ind+1)
end

def decode(x, r, ind)
    return if ind>=Len
    c=PS.index{|i| r*i/Tot>x }-1
    OutString[ind]=c

    lo, hi = lo_hi(c, r)
    decode(x-lo, hi-lo, ind+1)
end

r0=2**180
puts TestString
encoded=encode(r0, 0)
puts encoded
decode(encoded, r0, 0)
puts OutString

p TestString.size*8
p encoded.to_s(2).size
p OutString==TestString