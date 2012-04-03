#convert an integer to a binary encoding using elias gamma encoding
#this is needed because the number of bits in this integer is unknown to the decompressor.
def int2bits(x)
	abort('cant represent negative numbers') if x<0
	return [] if x==0
	
	bits=[]
	while x>0
		bits.unshift(x%2)
		x/=2
	end
	[0]*(bits.size-1)+bits
end

#convert some bits to the an integer using elias gamma encoding
#note modifies bits to be remainer of the bit stream
def bits2int(bits)
	i=0
	loop {
		return 0 if bits.empty?
		break if bits.shift==1
		i+=1
	}
	
	x=1
	i.times { x=x*2+bits.shift }
	x
end