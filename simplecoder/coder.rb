require 'elias_gamma'
require 'util'

#this is the number of bits used in computations, although the results are stored in a longer integer
Nbits = 32
N=2**Nbits

def encode(string, predictor)
	lo=0
	r=N
	nbits=Nbits

	string.each_byte{|c|
		cum=predictor.get_ranges()
		predictor.set_next_symbol(c)
		
		lo+=r*cum[c]/cum[256]
		r=r*cum[c+1]/cum[256]-r*cum[c]/cum[256]

		while r<N
			r*=2
			lo*=2
			nbits+=1
		end
	}
	
	bits=[]
	hi=lo+r-1
	#todo what if lo=000000000000 ?? could pick 0 instead
	i=nbits-1
	while lo[i]==hi[i]
		bits << hi[i]
		i-=1
	end
	bits << 1 #(could be implicit if it werent for bytes conversion)
	bits2str(int2bits(string.length)+bits)
end

def decode(string, predictor)
	bits=str2bits(string)
	len=bits2int(bits)

	out=''
	x=0
	r=1
	len.times{
		while r<N
			r*=2
			x=x*2+(bits.shift||0)
		end
		
		cum=predictor.get_ranges()
		out << c=cum.index{|i| r*i/cum[256]>x }-1
		predictor.set_next_symbol(c)
	
		x-=r*cum[c]/cum[256]
		r=r*cum[c+1]/cum[256]-r*cum[c]/cum[256]
	}
	out
end
