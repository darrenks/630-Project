TestString='this is a test string, how well does it compress?'
counts=256.times.map{|i|TestString.count(i.chr)}
s=0; Cum=[0]+counts.map{|i|s+=i}

#this is the number of bits used in computations, although the results are stored in a longer integer (for now)
N=2**Nbits=32

def encode(string)
	lo=0
	r=N
	nbits=Nbits

	string.each_byte{|c|
		lo+=r*Cum[c]/Cum[256]
		r=r*Cum[c+1]/Cum[256]-r*Cum[c]/Cum[256]

		while r<N
			r*=2
			lo*=2
			nbits+=1
		end
	}
	
	bits=[]
	hi=lo+r-1
	i=nbits-1
	while lo[i]==hi[i]
		bits<<hi[i]
		i-=1
	end
	
	bits<<1
	bits
end

def decode(bits)
	out=''
	x=0
	r=1
	TestString.size.times{
		while r<N
			r*=2
			x=x*2+(bits.shift||0)
		end
		
		out<<c=Cum.index{|i| r*i/Cum[256]>x }-1
	
		x-=r*Cum[c]/Cum[256]
		r=r*Cum[c+1]/Cum[256]-r*Cum[c]/Cum[256]
	}
	out
end

puts TestString
p encoded=encode(TestString)
puts decoded=decode(encoded.dup)

p TestString.size*8
p encoded.size
p decoded==TestString