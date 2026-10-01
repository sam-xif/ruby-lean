# block-destr
o=Object.new;def o.to_ary;p :convert;[1,2];end;p proc{|(a,b)|[a,b]}.call(o);p ->((a,b)){[a,b]}.call(o)

# block-missing-nested
a=99;b=98;p proc{|(a,b)|[a,b]}.call;p [a,b]

# block-lenient-extra
p proc{|(a,b)|[a,b]}.call([1,2],9);p proc{|(a,b),c|[a,b,c]}.call([[1,2],3])

# block-lambda-arity
f=->((a,b)){[a,b]};[[],[[1,2]],[[1,2],3]].each{|args|begin;p f.call(*args);rescue=>e;p [e.class,e.message];end}

# block-yield-destructure
o=Object.new;def o.to_ary;p :convert;[1,2];end;def emit(o);yield o;end;p emit(o){|(a,b)|[a,b]}

# block-map-destructure
p [[1,2],[3]].map{|(a,b)|[a,b]};p [[[1,2],3]].map{|((a,b),c)|[a,b,c]}

# block-rest-post
p proc{|(a,*b,c,d)|[a,b,c,d]}.call([1]);p proc{|(a,*b,c,d)|[a,b,c,d]}.call([1,2]);p proc{|(a,*b,c,d)|[a,b,c,d]}.call([1,2,3,4])

# block-return-conversion
def f;o=Object.new;o.define_singleton_method(:to_ary){return :done};[o].each{|(a,b)|p :wrong};end;p f()

# block-redo
o=Object.new;def o.to_ary;p :convert;[1,2];end;n=0;p proc{|(a,b)|n+=1;a+=n;redo if n<2;[a,b,n]}.call(o)

# block-next
o=Object.new;def o.to_ary;[1,2];end;p [o].map{|(a,b)|next a+b}

# block-captured-local
a=99;b=98;o=Object.new;def o.to_ary;[1,2];end;p [o].map{|(a,b)|p [a,b];a=3};p [a,b]

# block-ignored-rest-conversion
o=Object.new;def o.to_ary;p :convert;[1,2];end;p proc{|(*)|:body}.call(o)

nil
