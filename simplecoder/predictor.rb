# a simple byte predicter
# it thinks that substrings that we have seen before are likely to occur again
# todo it is horribly inefficient
class Predictor
	def initialize
		@sofar=[]
	end
	
	def set_next_symbol(sym)
		@sofar<<sym
	end
	
	def get_ranges()
		counts=[2]*128+[1]*128
		(@sofar.size-1).downto(0){|i|
			1.upto(i){|j|
				break unless @sofar[i-j]==@sofar[-j]
				counts[@sofar[i]]+=10*j
			}
		}
		
		sum=0
		[0]+counts.map{|i|sum+=i}
	end
end
