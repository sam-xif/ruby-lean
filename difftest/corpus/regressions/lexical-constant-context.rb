# L283: lexical constant context.

# eval-constant
class Scope1C;end
Scope1C.class_eval {Scope1X=1;class Scope1Nested;end}
p [Object.const_defined?(:Scope1X,false),Scope1C.const_defined?(:Scope1X,false),Object.const_defined?(:Scope1Nested,false),Scope1C.const_defined?(:Scope1Nested,false)]

# eval-constant-nested
module Scope2Outer;class Scope2C;end;Scope2C.class_eval {Scope2X=1;class Scope2Nested;end};end
p [Scope2Outer.const_defined?(:Scope2X,false),Scope2Outer::Scope2C.const_defined?(:Scope2X,false),Scope2Outer.const_defined?(:Scope2Nested,false)]

# single-constant-ancestor
class Scope3P;Scope3X=4;end;class Scope3C<Scope3P;def self.read;Scope3X;end;end;p Scope3C.read

# constant-priority
Scope4X=:top;class Scope4P;Scope4X=:parent;end;class Scope4C<Scope4P;def self.read;Scope4X;end;end;p Scope4C.read;module Scope4M;def self.read;Scope4X;end;end;p Scope4M.read;module Scope4Outer;Scope4X=:outer;class Scope4C<Scope4P;def self.read;Scope4X;end;end;end;p Scope4Outer::Scope4C.read

# qualified-constant-cref
module Scope5Q;end;module Scope5Outer;Scope5X=:outer;class Scope5Q::Scope5C;def self.read;Scope5X;end;end;end;p Scope5Q::Scope5C.read

# constant-eval-reading
class Scope6C;Scope6X=:class;end;Scope6X=:outer;p Scope6C.class_eval {Scope6X};class Scope6P;Scope6X=:parent;end;class Scope6D<Scope6P;def self.read;defined?(Scope6X);end;end;p Scope6D.read

# const-basic-object
Scope7X=1;class BasicObject;def self.read;Scope7X;end;end;begin;p BasicObject.read;rescue=>e;p e.message;end
