# L289: object inspect control.

# object-cycle
o=Object.new;o.instance_variable_set(:@self,o);p o;nil

# object-cycle-hook
class CInspectCase1;def initialize;@self=self;end;def instance_variables_to_inspect;p :hook;nil;end;end;p CInspectCase1.new;nil

# inspect-pair-cycle
a=Object.new;b=Object.new;a.instance_variable_set(:@b,b);b.instance_variable_set(:@a,a);p a;nil

# inspect-cycle-empty-hook
class CInspectCase3;def initialize;@self=self;@n=0;end;def instance_variables_to_inspect;@n+=1;@n==1 ? [:@self] : [];end;end;p CInspectCase3.new;nil

# inspect-throw
o=Object.new;def o.instance_variables_to_inspect;throw :done,7;end;p catch(:done){p o};nil

# inspect-retry-after-raise
class VInspectCase5;def inspect;$n+=1;raise "first" if $n==1;"VInspectCase5";end;end;$n=0;o=Object.new;o.instance_variable_set(:@a,VInspectCase5.new);begin;p o;rescue=>e;p e.message;end;p o;nil

# inspect-existing-dollar-bang
begin;raise "outer";rescue;obj=Object.new;def obj.instance_variables_to_inspect;p $!.message;[];end;p obj;p $!.message;end;nil

# inspect-frozen-error
o=Object.new;def o.instance_variables_to_inspect;p :hook;[];end;o.freeze;begin;o.instance_variable_set(:@a,1);rescue=>e;p [e.class,e.message];end

nil
