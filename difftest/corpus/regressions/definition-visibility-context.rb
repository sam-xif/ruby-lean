# L283: definition visibility context.

# block-private
class Scope1C;private;1.times {def a;1;end};end
p [Scope1C.method_defined?(:a),Scope1C.private_method_defined?(:a)]

# block-changes-visibility
class Scope2C;1.times {private;def a;1;end};def b;2;end;end
p [Scope2C.private_method_defined?(:a),Scope2C.private_method_defined?(:b)]

# proc-late-visibility
class Scope3C;Scope3P=proc {def a;1;end};private;Scope3P.call;end
p Scope3C.private_method_defined?(:a)

# proc-retired-visibility
class Scope4C;private;Scope4P=proc {def a;1;end};end
Scope4C::Scope4P.call;p Scope4C.private_method_defined?(:a)

# method-private-reset
class Scope5C;private;def self.make;def x;1;end;end;end
Scope5C.make;p [Scope5C.method_defined?(:x),Scope5C.private_method_defined?(:x)]

# eval-private-reset
class Scope6C;private;class_eval {def a;1;end};def b;2;end;end
p [Scope6C.method_defined?(:a),Scope6C.private_method_defined?(:b)]

# eval-visibility-no-leak
class Scope7C;class_eval {private;def a;1;end};def b;2;end;end
p [Scope7C.private_method_defined?(:a),Scope7C.method_defined?(:b)]

# dm-private-target
class Scope8C;end;class Scope8D;private;Scope8C.define_method(:x){1};Scope8C.attr_reader(:a);end
p [Scope8C.method_defined?(:x),Scope8C.private_method_defined?(:x),Scope8C.method_defined?(:a),Scope8C.private_method_defined?(:a)]

# dm-private-own
class Scope9C;private;define_method(:x){1};attr_reader(:a);end
p [Scope9C.private_method_defined?(:x),Scope9C.private_method_defined?(:a)]

# method-visibility-ignored
class Scope10C;def self.make(flag);private if flag;def x;1;end;end;end;Scope10C.make(true);p Scope10C.private_method_defined?(:x);Scope10C.send(:remove_method,:x);Scope10C.make(false);p Scope10C.method_defined?(:x)

# main-dm-visibility
private;define_method(:root_dm){1};p [Object.private_method_defined?(:root_dm),Object.method_defined?(:root_dm)];public;def root_def;2;end;p Object.method_defined?(:root_def)
