#use a long integer instead of bits

TestString='this is a test string, how well does it compress'
counts=256.times.map{|i|TestString.count(i.chr)}
s=0; PS=[0]+counts.map{|i|s+=i}
Tot = PS[256]

N=2**32

def encode(string)
	lo=0
	
	#this loop finds the smallest power of 2, r0 that is big enough to compress
	#we can skip proving this part, by just assuming r never is 0
	r0=1
	begin
        lo=0
        r=r0
    
        string.each_byte{|c|		
            lo+=r*PS[c]/Tot
            r=r*PS[c+1]/Tot-r*PS[c]/Tot
        }
        
        r0=r0*2
	end while r==0
	p r0.to_s(2).size
	
	[lo,r0/2]
end

def decode(x,r)
	out=''
	TestString.size.times{		
		out<<c=PS.index{|i| r*i/Tot>x }-1
	
		x-=r*PS[c]/Tot
		r=r*PS[c+1]/Tot-r*PS[c]/Tot
	}
	out
end

puts TestString
encoded,r0=encode(TestString)
puts encoded
puts decoded=decode(encoded, r0)

p TestString.size*8
p encoded.to_s(2).size
p decoded==TestString