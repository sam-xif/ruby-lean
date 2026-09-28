# L283: nested definition targets.

# nested-self
class Scope1C;def self.make;def x;1;end;end;end
p Scope1C.make;p [Scope1C.method_defined?(:x),Scope1C.respond_to?(:x)];p Scope1C.new.x

# nested-proc
class Scope2C;def self.make;proc {def x;1;end};end;end
p Scope2C.make.call;p [Scope2C.method_defined?(:x),Scope2C.respond_to?(:x)];p Scope2C.new.x

# nested-eigen
class Scope3C;class<<self;def make;def x;1;end;end;end;end
p Scope3C.make;p [Scope3C.method_defined?(:x),Scope3C.respond_to?(:x)];p Scope3C.x

# nested-external
o=Object.new;def o.make;def generated;1;end;end
p o.make;p [Object.method_defined?(:generated),Object.private_method_defined?(:generated),o.respond_to?(:generated)]

# nested-module
module Scope5M;def make;def x;1;end;end;end
class Scope5C;include Scope5M;end;p Scope5C.new.make;p [Scope5M.method_defined?(:x),Scope5C.new.x]

# nested-eval-method
class Scope6C;end
Scope6C.class_eval {def self.make;proc {def x;1;end};end}
p Scope6C.make.call;p [Scope6C.method_defined?(:x),Scope6C.respond_to?(:x),Object.method_defined?(:x)]

# nested-alias
class Scope7C
 def x;1;end
 def self.make;alias y x;end
end
p Scope7C.make;p Scope7C.new.y

# nested-undef
class Scope8C
 def x;1;end
 def self.remove;undef x;end
end
p Scope8C.remove;p Scope8C.method_defined?(:x)
