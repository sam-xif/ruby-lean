# L289: object inspect hooks.

# plain-response
o=Object.new;def o.respond_to?(*a);p a;false;end;p o;nil

# plain-private-hook
class CInspectCase1;def initialize;@a=1;@b=2;end;private;def instance_variables_to_inspect;p :hook;[:@b,:@a,:@b];end;end;p CInspectCase1.new;nil

# plain-nil-hook
class CInspectCase2;def initialize;@a=1;end;def instance_variables_to_inspect;p :hook;nil;end;end;p CInspectCase2.new;nil

# plain-bad-hook
class CInspectCase3;def instance_variables_to_inspect;7;end;end;begin;p CInspectCase3.new;rescue=>e;p [e.class,e.message];end

# plain-hook-filter
class CInspectCase4;def initialize;@a=1;@b=2;end;def instance_variables_to_inspect;[1,nil,"@a",:a,:@unknown,:@b];end;end;p CInspectCase4.new;nil

# plain-hook-empty
class CInspectCase5;def initialize;@a=1;end;def instance_variables_to_inspect;[];end;end;p CInspectCase5.new;nil

# plain-response-lie
o=Object.new;def o.respond_to?(*a);p a;true;end;def o.method_missing(*a);p a;[];end;p o;nil

# plain-hook-raise
o=Object.new;def o.instance_variables_to_inspect;raise "hook";end;begin;p o;rescue=>e;p [e.class,e.message];end

# plain-hook-mutation
class CInspectCase8;def initialize;@a=1;end;def instance_variables_to_inspect;@b=2;nil;end;end;p CInspectCase8.new;nil

# hook-super
class CInspectCase9;def instance_variables_to_inspect;p :hook;super;end;end;p CInspectCase9.new;nil

# hook-undef-mm
class CInspectCase10;undef instance_variables_to_inspect;def respond_to_missing?(n,*a);p [n,a];true;end;def method_missing(*a);p a;[];end;end;p CInspectCase10.new;nil

# hook-undef-mm-raise
class CInspectCase11;undef instance_variables_to_inspect;def method_missing(*a);p a;super;end;end;p CInspectCase11.new;nil

# hook-one-response
o=Object.new;def o.respond_to?(n);p n;false;end;p o;nil

# plain-alias-inspect
class CInspectCase13;alias show inspect;def instance_variables_to_inspect;p :hook;[];end;end;p CInspectCase13.new.show

# plain-arity
o=Object.new;def o.instance_variables_to_inspect;raise "wrong";end;begin;o.inspect(1);rescue=>e;p [e.class,e.message];end

# inspect-hook-false
o=Object.new;def o.instance_variables_to_inspect;false;end;begin;p o;rescue=>e;p [e.class,e.message];end

# inspect-hook-toary
class AInspectCase16;def to_ary;raise "wrong";end;end;o=Object.new;def o.instance_variables_to_inspect;AInspectCase16.new;end;begin;p o;rescue=>e;p [e.class,e.message];end

# inspect-hook-undef-response-true
class CInspectCase17;undef instance_variables_to_inspect;def respond_to?(*a);p a;true;end;def method_missing(*a);p a;raise NoMethodError,"claimed";end;end;begin;p CInspectCase17.new;rescue=>e;p [e.class,e.message];end

# inspect-hook-mutate-response
o=Object.new;def o.respond_to?(*a);p a;def instance_variables_to_inspect;p :new_hook;[];end;true;end;p o;nil

# inspect-hook-super-nil
o=Object.new;def o.instance_variables_to_inspect;p super;[];end;p o;nil

# inspect-hook-private-direct
o=Object.new;p o.send(:instance_variables_to_inspect);p o.respond_to?(:instance_variables_to_inspect);p o.respond_to?(:instance_variables_to_inspect,true);begin;o.instance_variables_to_inspect;rescue=>e;p [e.class,e.message];end

# inspect-hook-arity
o=Object.new;begin;o.send(:instance_variables_to_inspect,1);rescue=>e;p [e.class,e.message];end

# inspect-hook-lookup-after-undef
o=Object.new;o.instance_variable_set(:@a,1);def o.respond_to?(*a);class<<self;undef instance_variables_to_inspect;end;true;end;def o.method_missing(*a);p a;[];end;p o;nil

nil
