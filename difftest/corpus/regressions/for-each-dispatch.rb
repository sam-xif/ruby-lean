# L288: for each dispatch.

# array-each-override
a=[1,2];def a.each;p :each;yield 7;:finished;end;p(for x in a;p x;end);p x

# array-live-growth
a=[1];for x in a;p x;a<<2 if x==1;end;p x

# array-live-replace
a=[1,2];for x in a;p x;a[1]=9 if x==1;end

# custom-each
o=Object.new;def o.each;yield 1,2;yield 3;:finished;end;p(for a,b in o;p [a,b];end);p [a,b]

# private-each
begin;class EForCase4;private;def each;yield 7;:finished;end;end;p(for x in EForCase4.new;p x;end);p x;rescue=>err;p [err.class,err.message];end

# for-self-private
class EForCase5;def run;for x in self;p x;end;end;private;def each;yield 7;end;end;begin;p EForCase5.new.run;rescue=>e;p [e.class,e.message];end

# for-protected
class EForCase6;def run(other);for x in other;p x;end;end;protected;def each;yield 7;:done;end;end;p EForCase6.new.run(EForCase6.new)

# for-mm
o=Object.new;def o.method_missing(n,*a,&b);p n;b.call(7);:done;end;p(for x in o;p x;end);p x

# for-mm-private
class EForCase8;private;def each;raise "wrong";end;def method_missing(n,*a,&b);p n;b.call(7);:done;end;end;p(for x in EForCase8.new;p x;end)

# for-undef-each
a=[1,2];class<<a;undef each;end;begin;for x in a;p :wrong;end;rescue=>e;p [e.class,e.message];end

# for-hash
h={a:1,b:2};p(for x in h;p x;end);p(for k,v in h;p [k,v];end);p [k,v]

# for-range
p(for x in 2..4;p x;end);p x

# for-range-override
class Range;def each;yield 7;:done;end;end;p(for x in 1..3;p x;end)

nil
