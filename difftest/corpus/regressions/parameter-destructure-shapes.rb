# method-missing-nested
def f((a,(b,c)));p [a,b,c];end;f([])

# method-overlapping-post
def f((a,*b,c,d));p [a,b,c,d];end;f([1]);f([1,2]);f([1,2,3])

# method-nested-order
o=Object.new;def o.to_ary;p :outer;[1,self];end;def f((a,(b,c)));p [a,b,c.class];end;f(o)

# destructure-shapes
def shape_0((a,b));[a,b];end
p [shape_0([]), proc{|(a,b)|[a,b]}.call([]), ->((a,b)){[a,b]}.call([])]
p [shape_0([1]), proc{|(a,b)|[a,b]}.call([1]), ->((a,b)){[a,b]}.call([1])]
p [shape_0([1,2]), proc{|(a,b)|[a,b]}.call([1,2]), ->((a,b)){[a,b]}.call([1,2])]
p [shape_0([1,2,3]), proc{|(a,b)|[a,b]}.call([1,2,3]), ->((a,b)){[a,b]}.call([1,2,3])]
p [shape_0([1,2,3,4]), proc{|(a,b)|[a,b]}.call([1,2,3,4]), ->((a,b)){[a,b]}.call([1,2,3,4])]
p [shape_0([[1,2],[3,4],5]), proc{|(a,b)|[a,b]}.call([[1,2],[3,4],5]), ->((a,b)){[a,b]}.call([[1,2],[3,4],5])]
p [shape_0([nil,nil,nil]), proc{|(a,b)|[a,b]}.call([nil,nil,nil]), ->((a,b)){[a,b]}.call([nil,nil,nil])]
def shape_1((*a,b,c));[a,b,c];end
p [shape_1([]), proc{|(*a,b,c)|[a,b,c]}.call([]), ->((*a,b,c)){[a,b,c]}.call([])]
p [shape_1([1]), proc{|(*a,b,c)|[a,b,c]}.call([1]), ->((*a,b,c)){[a,b,c]}.call([1])]
p [shape_1([1,2]), proc{|(*a,b,c)|[a,b,c]}.call([1,2]), ->((*a,b,c)){[a,b,c]}.call([1,2])]
p [shape_1([1,2,3]), proc{|(*a,b,c)|[a,b,c]}.call([1,2,3]), ->((*a,b,c)){[a,b,c]}.call([1,2,3])]
p [shape_1([1,2,3,4]), proc{|(*a,b,c)|[a,b,c]}.call([1,2,3,4]), ->((*a,b,c)){[a,b,c]}.call([1,2,3,4])]
p [shape_1([[1,2],[3,4],5]), proc{|(*a,b,c)|[a,b,c]}.call([[1,2],[3,4],5]), ->((*a,b,c)){[a,b,c]}.call([[1,2],[3,4],5])]
p [shape_1([nil,nil,nil]), proc{|(*a,b,c)|[a,b,c]}.call([nil,nil,nil]), ->((*a,b,c)){[a,b,c]}.call([nil,nil,nil])]
def shape_2((a,*b,c,d));[a,b,c,d];end
p [shape_2([]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([]), ->((a,*b,c,d)){[a,b,c,d]}.call([])]
p [shape_2([1]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([1]), ->((a,*b,c,d)){[a,b,c,d]}.call([1])]
p [shape_2([1,2]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([1,2]), ->((a,*b,c,d)){[a,b,c,d]}.call([1,2])]
p [shape_2([1,2,3]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([1,2,3]), ->((a,*b,c,d)){[a,b,c,d]}.call([1,2,3])]
p [shape_2([1,2,3,4]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([1,2,3,4]), ->((a,*b,c,d)){[a,b,c,d]}.call([1,2,3,4])]
p [shape_2([[1,2],[3,4],5]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([[1,2],[3,4],5]), ->((a,*b,c,d)){[a,b,c,d]}.call([[1,2],[3,4],5])]
p [shape_2([nil,nil,nil]), proc{|(a,*b,c,d)|[a,b,c,d]}.call([nil,nil,nil]), ->((a,*b,c,d)){[a,b,c,d]}.call([nil,nil,nil])]
def shape_3((a,(b,*c,d),*e,f));[a,b,c,d,e,f];end
p [shape_3([]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([])]
p [shape_3([1]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([1]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([1])]
p [shape_3([1,2]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([1,2]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([1,2])]
p [shape_3([1,2,3]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([1,2,3]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([1,2,3])]
p [shape_3([1,2,3,4]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([1,2,3,4]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([1,2,3,4])]
p [shape_3([[1,2],[3,4],5]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([[1,2],[3,4],5]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([[1,2],[3,4],5])]
p [shape_3([nil,nil,nil]), proc{|(a,(b,*c,d),*e,f)|[a,b,c,d,e,f]}.call([nil,nil,nil]), ->((a,(b,*c,d),*e,f)){[a,b,c,d,e,f]}.call([nil,nil,nil])]
def shape_4((a,*,b));[a,b];end
p [shape_4([]), proc{|(a,*,b)|[a,b]}.call([]), ->((a,*,b)){[a,b]}.call([])]
p [shape_4([1]), proc{|(a,*,b)|[a,b]}.call([1]), ->((a,*,b)){[a,b]}.call([1])]
p [shape_4([1,2]), proc{|(a,*,b)|[a,b]}.call([1,2]), ->((a,*,b)){[a,b]}.call([1,2])]
p [shape_4([1,2,3]), proc{|(a,*,b)|[a,b]}.call([1,2,3]), ->((a,*,b)){[a,b]}.call([1,2,3])]
p [shape_4([1,2,3,4]), proc{|(a,*,b)|[a,b]}.call([1,2,3,4]), ->((a,*,b)){[a,b]}.call([1,2,3,4])]
p [shape_4([[1,2],[3,4],5]), proc{|(a,*,b)|[a,b]}.call([[1,2],[3,4],5]), ->((a,*,b)){[a,b]}.call([[1,2],[3,4],5])]
p [shape_4([nil,nil,nil]), proc{|(a,*,b)|[a,b]}.call([nil,nil,nil]), ->((a,*,b)){[a,b]}.call([nil,nil,nil])]
def shape_5(((a,b),c));[a,b,c];end
p [shape_5([]), proc{|((a,b),c)|[a,b,c]}.call([]), ->(((a,b),c)){[a,b,c]}.call([])]
p [shape_5([1]), proc{|((a,b),c)|[a,b,c]}.call([1]), ->(((a,b),c)){[a,b,c]}.call([1])]
p [shape_5([1,2]), proc{|((a,b),c)|[a,b,c]}.call([1,2]), ->(((a,b),c)){[a,b,c]}.call([1,2])]
p [shape_5([1,2,3]), proc{|((a,b),c)|[a,b,c]}.call([1,2,3]), ->(((a,b),c)){[a,b,c]}.call([1,2,3])]
p [shape_5([1,2,3,4]), proc{|((a,b),c)|[a,b,c]}.call([1,2,3,4]), ->(((a,b),c)){[a,b,c]}.call([1,2,3,4])]
p [shape_5([[1,2],[3,4],5]), proc{|((a,b),c)|[a,b,c]}.call([[1,2],[3,4],5]), ->(((a,b),c)){[a,b,c]}.call([[1,2],[3,4],5])]
p [shape_5([nil,nil,nil]), proc{|((a,b),c)|[a,b,c]}.call([nil,nil,nil]), ->(((a,b),c)){[a,b,c]}.call([nil,nil,nil])]
def shape_6((*));:body;end
p [shape_6([]), proc{|(*)|:body}.call([]), ->((*)){:body}.call([])]
p [shape_6([1]), proc{|(*)|:body}.call([1]), ->((*)){:body}.call([1])]
p [shape_6([1,2]), proc{|(*)|:body}.call([1,2]), ->((*)){:body}.call([1,2])]
p [shape_6([1,2,3]), proc{|(*)|:body}.call([1,2,3]), ->((*)){:body}.call([1,2,3])]
p [shape_6([1,2,3,4]), proc{|(*)|:body}.call([1,2,3,4]), ->((*)){:body}.call([1,2,3,4])]
p [shape_6([[1,2],[3,4],5]), proc{|(*)|:body}.call([[1,2],[3,4],5]), ->((*)){:body}.call([[1,2],[3,4],5])]
p [shape_6([nil,nil,nil]), proc{|(*)|:body}.call([nil,nil,nil]), ->((*)){:body}.call([nil,nil,nil])]
nil


nil
