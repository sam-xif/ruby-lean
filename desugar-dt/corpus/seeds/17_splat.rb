# splat: in call args, in array literals, rest params (def + block), and massign
def take(a, b, c)
  [a, b, c]
end

def variadic(first, *rest)
  [first, rest]
end

xs = [2, 3]
call_result   = take(1, *xs)            # splat in call args -> take(1,2,3)
array_result  = [0, *xs, 4, *[5, 6]]    # splat in array literal
var_result    = variadic(10, 20, 30)    # rest param collects [20, 30]

# multiple assignment with rest target and splat RHS
a, *b, c = 1, 2, 3, 4, 5                 # a=1, b=[2,3,4], c=5
head, *tail = *xs, 99                    # splat RHS: [2,3,99] -> head=2, tail=[3,99]

# rest-target underflow (Ruby fills post targets front-to-back; rest may be empty)
p1, q1, *r1 = [9]                         # p1=9, q1=nil, r1=[]
lead, mid, tailz, *rest0 = [0]            # lead=0, mid=nil, tailz=nil, rest0=[]
*sa, sb, sc = [10, 20, 30, 40]           # overflow: sa=[10,20], sb=30, sc=40

# block with rest param
sums = [[1, 2, 3], [4, 5]].map { |first, *others| [first, others] }

p [call_result, array_result, var_result, a, b, c, head, tail, sums,
   p1, q1, r1, lead, mid, tailz, rest0, sa, sb, sc]
