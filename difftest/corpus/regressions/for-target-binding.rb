# L288: for target binding.

# for-packed-yields
class EForCase0;def each;yield;yield 1;yield 1,2;yield [3,4];end;end;for x in EForCase0.new;p x;end;for x,y in EForCase0.new;p [x,y];end

# for-to-ary
o=Object.new;def o.to_ary;p :convert;[1,2];end;for a,b in [o];p [a,b];end

# for-to-ary-private
class PairForCase2;private;def to_ary;p :convert;[7,8];end;end;for x,y in [PairForCase2.new];p [x,y];end

# for-to-ary-nil
o=Object.new;def o.to_ary;p :convert;nil;end;for x,y in [o];p [x.equal?(o),y];end;nil

# for-to-ary-bad
o=Object.new;def o.to_ary;7;end;begin;for x,y in [o];p :wrong;end;rescue=>e;p [e.class,e.message];end

# for-to-ary-respond
o=Object.new;def o.respond_to?(*a);p a;false;end;def o.to_ary;raise "wrong";end;for x,y in [o];p [x.equal?(o),y];end;nil

# for-single-no-conversion
o=Object.new;def o.to_ary;raise "wrong";end;for x in [o];p x.equal?(o);end

# for-nonlocal-targets
class CForCase7;def f;for @x,$y in [[1,2],[3,4]];p [@x,$y];end;p @x;end;end;CForCase7.new.f;for CForForCase7 in [1,2];p CForForCase7;end

# for-gvar-target
p(for $x in [1,2];p $x;end);p $x

# for-cvar-target
class CForCase9;for @@x in [1,2];p @@x;end;def self.x;@@x;end;end;p CForCase9.x

# for-frozen-target
class CForCase10;def run;freeze;for @x in [1];p :wrong;end;end;def inspect;"TARGET";end;end;begin;CForCase10.new.run;rescue=>e;p [e.class,e.message];end

# for-one-comma
class EForCase11;def each;yield [1,2];yield 3,4;end;end;for x, in EForCase11.new;p x;end;p x

# for-one-comma-ivars
class CForCase12;def run;for @x, in [[1,2],3];p @x;end;end;end;CForCase12.new.run

# for-one-comma-bad
o=Object.new;def o.to_ary;7;end;begin;for x, in [o];p :wrong;end;rescue=>e;p [e.class,e.message];end

# for-multi-zero
class EForCase14;def each;yield;yield nil;yield 1,2;end;end;class NilClass;def to_ary;p :nil_convert;[7,8];end;end;for x,y in EForCase14.new;p [x,y];end

nil
