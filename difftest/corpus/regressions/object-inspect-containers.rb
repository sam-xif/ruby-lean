# L289: object inspect containers.

# nested-filter
class CInspectCase0;def initialize;@a=1;@b=2;end;def instance_variables_to_inspect;[:@b];end;end;p [CInspectCase0.new,{x:CInspectCase0.new}];nil

# hook-inspect-super
class CInspectCase1;def initialize;@a=1;end;def inspect;super;end;def instance_variables_to_inspect;[];end;end;p CInspectCase1.new;nil

# inspect-nested-container
class CInspectCase2;def initialize;@a=1;@b=2;end;def <=>(other);0;end;def instance_variables_to_inspect;p :hook;[:@b];end;end;p [CInspectCase2.new];p({a:CInspectCase2.new});p CInspectCase2.new..CInspectCase2.new;nil

# inspect-random
r=Random.new(1);r.instance_variable_set(:@a,1);def r.instance_variables_to_inspect;p :hook;nil;end;p r;nil

# inspect-generator
r=Enumerator::Generator.new{|y|y<<1};r.instance_variable_set(:@a,1);def r.instance_variables_to_inspect;p :hook;nil;end;p r;nil

# inspect-yielder
r=Enumerator::Yielder.new{|x|x};r.instance_variable_set(:@a,1);def r.instance_variables_to_inspect;p :hook;nil;end;p r;nil

# inspect-random-pure
r=Random.new(1);r.instance_variable_set(:@a,1);p r;nil

# inspect-generator-pure
r=Enumerator::Generator.new{|y|y<<1};r.instance_variable_set(:@a,1);p r;nil

# inspect-yielder-pure
r=Enumerator::Yielder.new{|x|x};r.instance_variable_set(:@a,1);p r;nil

# inspect-nested-super-native
class AInspectCase9<Array;def initialize;@a=1;end;def inspect;super;end;def instance_variables_to_inspect;raise "unused";end;end;p AInspectCase9.new;nil

# inspect-main
def instance_variables_to_inspect;raise "wrong";end;p self;p self.inspect

nil
