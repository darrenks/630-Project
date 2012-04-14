TestString='this is a test string, how well does it compress'
counts=256.times.map{|i|TestString.count(i.chr)}
s=0; PS=[0]+counts.map{|i|s+=i}
Tot = PS[256]

N=2**32

def encode(string)
	lo=0
	r=1
	nbits=0

	string.each_byte{|c|
		while r<N
			r*=2
			lo*=2
			nbits+=1
		end
		
		lo+=r*PS[c]/Tot
		r=r*PS[c+1]/Tot-r*PS[c]/Tot

	}
	
	nbits.times.map{|i| lo[nbits-i-1] }
end

def decode(bits)
	out=''
	x=0
	r=1
	TestString.size.times{
		while r<N
			r*=2
			x=x*2+bits.shift
		end
		
		out<<c=PS.index{|i| r*i/Tot>x }-1
	
		x-=r*PS[c]/Tot
		r=r*PS[c+1]/Tot-r*PS[c]/Tot
		
	}
	out
end

puts TestString
p encoded=encode(TestString)
puts decoded=decode(encoded.dup)

p TestString.size*8
p encoded.size
p decoded==TestString