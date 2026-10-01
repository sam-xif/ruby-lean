# L289: object inspect fields.

# plain-native-ivars
o=Object.new;o.instance_variable_set(:@a,1);def o.instance_variables;raise "wrong ivars";end;def o.instance_variable_get(*a);raise "wrong get";end;p o;nil

# ivar-write-order
o=Object.new;o.instance_variable_set(:@a,1);o.instance_variable_set(:@b,2);o.instance_variable_set(:@a,3);p o.instance_variables;p o;nil

# ivar-syntax-order
class CInspectCase2;def initialize;@a=1;@b=2;@a=3;end;end;p CInspectCase2.new;nil

# buffer-values
class VInspectCase3;def inspect;$o.instance_variable_set(:@b,9);$o.instance_variable_set(:@c,10);"VInspectCase3";end;end;$o=Object.new;$o.instance_variable_set(:@a,VInspectCase3.new);$o.instance_variable_set(:@b,2);p $o;p $o;nil

# live-filter
$filter=[:@a];class VInspectCase4;def inspect;$filter<<:@b;"VInspectCase4";end;end;o=Object.new;o.instance_variable_set(:@a,VInspectCase4.new);o.instance_variable_set(:@b,2);def o.instance_variables_to_inspect;$filter;end;p o;nil

# inspect-filter-pop
$filter=[:@a,:@b];class VInspectCase5;def inspect;$filter.pop;$filter.pop;"VInspectCase5";end;end;o=Object.new;o.instance_variable_set(:@a,VInspectCase5.new);o.instance_variable_set(:@b,2);def o.instance_variables_to_inspect;$filter;end;p o;nil

# inspect-native-ivars-slow
class VInspectCase6;def inspect;"VInspectCase6";end;end;o=Object.new;o.instance_variable_set(:@a,VInspectCase6.new);def o.instance_variables;raise "wrong ivars";end;def o.instance_variable_get(*a);raise "wrong get";end;p o;nil

# field-inspect-nonstr
class VInspectCase7;def inspect;7;end;end;o=Object.new;o.instance_variable_set(:@a,VInspectCase7.new);p o;nil

# field-inspect-bad-tos
class WInspectCase8;def to_s;7;end;end;class VInspectCase8;def inspect;WInspectCase8.new;end;end;o=Object.new;o.instance_variable_set(:@a,VInspectCase8.new);p o;nil

# inspect-field-return-string
class SInspectCase9<String;def to_s;raise "wrong";end;end;class VInspectCase9;def inspect;SInspectCase9.new("VInspectCase9");end;end;o=Object.new;o.instance_variable_set(:@a,VInspectCase9.new);p o;nil

# inspect-head-class-overrides
class CInspectCase10;def self.to_s;raise "wrong";end;def class;raise "wrong";end;def initialize;@a=1;end;def instance_variables_to_inspect;nil;end;end;p CInspectCase10.new;nil

# inspect-native-hook-array-subclass
class AInspectCase11<Array;def each;raise "wrong";end;def length;raise "wrong";end;def include?(*a);raise "wrong";end;end;a=AInspectCase11.new;a<<:@a;o=Object.new;o.instance_variable_set(:@a,1);$list=a;def o.instance_variables_to_inspect;$list;end;p o;nil

# inspect-filter-symbol-overrides
class Symbol;alias __inspect_original_equal ==;alias __inspect_original_to_s to_s;end;class Symbol;def ==(*a);raise "wrong";end;def to_s;raise "wrong";end;end;o=Object.new;o.instance_variable_set(:@a,1);def o.instance_variables_to_inspect;[:@a];end;p o;nil;class Symbol;alias == __inspect_original_equal;alias to_s __inspect_original_to_s;end

nil
