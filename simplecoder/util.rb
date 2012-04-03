#convert an array of bits into a string
#must shift so that bits are aligned into the bytes correctly
def bits2str(bits)
	#first append 0 until size%8=0
	out=''
	until bits.empty?
		x=0
		8.times{ x=x*2+(bits.shift||0) }
		out<<x
	end
	out
end

#convert the string back into bits
#there may be more trailing zeros than before, but this does not matter since this bit string represents a fraction (finitely even)
def str2bits(str)
	str.unpack('B*')[0].split(//).map(&:to_i)
end
