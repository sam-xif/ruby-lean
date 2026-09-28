# method-to-ary
o=Object.new;def o.to_ary;p :convert;[1,2];end;def f((a,b));p [a,b];end;f(o)

# method-private-to-ary
class PairBindingCase1;private;def to_ary;p :convert;[1,2];end;end;def f((a,b));p [a,b];end;f(PairBindingCase1.new)

# method-to-ary-nil
o=Object.new;def o.to_ary;p :convert;nil;end;def f((a,b));p [a.class,b];end;f(o)

# method-to-ary-invalid
o=Object.new;def o.to_ary;p :convert;7;end;def f((a,b));p [a,b];end;begin;f(o);rescue=>e;p [e.class,e.message];end

# respond-false
o=Object.new;def o.respond_to?(*a);p a;false;end;def o.to_ary;p :wrong;[1,2];end;def f((a,b));p [a.class,b];end;f(o)

# missing
o=Object.new;def o.method_missing(n,*a);p n;[1,2];end;def f((a,b));p [a,b];end;f(o)

# array-to-ary
a=[1,2];def a.to_ary;raise "wrong";end;def f((a,b));p [a,b];end;f(a)

# bind-missing-nil
o=Object.new;def o.method_missing(n,*a);p n;nil;end;def f((a,b));p [a.class,b];end;f(o)

# bind-missing-bad
o=Object.new;def o.method_missing(n,*a);p n;9;end;def f((a,b));p :wrong;end;begin;f(o);rescue=>e;p [e.class,e.message];end

# bind-missing-super
o=Object.new;def o.method_missing(n,*a);p n;super;end;def f((a,b));p [a.class,b];end;f(o)

# bind-respond-missing
o=Object.new;def o.respond_to_missing?(*a);p a;true;end;def o.method_missing(n,*a);p n;[1,2];end;def f((a,b));p [a,b];end;f(o)

# bind-response-redefines
o=Object.new;def o.respond_to?(n,p=false);def self.to_ary;[8,9];end;true;end;def f((a,b));p [a,b];end;f(o)

# bind-undef-converter
class PairBindingCase12;def to_ary;raise "wrong";end;end;class ChildBindingCase12<PairBindingCase12;undef to_ary;end;def f((a,b));p [a.class,b];end;f(ChildBindingCase12.new)

# bind-array-subclass
class ABindingCase13<Array;def to_ary;raise "wrong";end;end;def f((a,b));p [a,b];end;a=ABindingCase13.new;a<<1<<2;f(a)

# bind-to-a-not-used
o=Object.new;def o.to_a;raise "wrong";end;def f((a,b));p [a.class,b];end;f(o)

# bind-two-callbacks
class PairBindingCase15;def initialize(n);@n=n;end;def to_ary;p @n;[@n,@n+1];end;end;def f((a,b),(c,d));p [a,b,c,d];end;f(PairBindingCase15.new(1),PairBindingCase15.new(3))

# bind-rescue-boundary
o=Object.new;def o.to_ary;raise "conversion";end;def f((a,b));p :body;rescue;p :wrong;ensure;p :wrong;end;begin;f(o);rescue=>e;p e.message;end

# bind-ensure
o=Object.new;def o.to_ary;begin;raise "conversion";ensure;p :converter_ensure;end;end;def f((a,b));p :wrong;end;begin;f(o);rescue=>e;p e.message;ensure;p :outer_ensure;end

# bind-throw
o=Object.new;def o.to_ary;throw :done,7;end;def f((a,b));p :wrong;end;p catch(:done){f(o)}

# nil-to-ary
class NilClass;def to_ary;p :convert;[1,2];end;end;def f((a,b));p [a,b];end;f(nil)

# bind-sparse-nested-nil
class NilClass;def to_ary;p :nil_convert;[1];end;end;def f((a,(b,c)));p [a,b,c];end;f([])

nil
