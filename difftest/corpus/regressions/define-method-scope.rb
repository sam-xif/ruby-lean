# L283: define method scope.

# nested-dm-root
class Scope1C;end;body=proc {def root_generated;1;end};Scope1C.define_method(:make,body)
p Scope1C.new.make;p [Scope1C.method_defined?(:root_generated),Object.method_defined?(:root_generated),Object.private_method_defined?(:root_generated)]

# nested-dm-class
class Scope2C;end
class Scope2D;Scope2BODY=proc {def x;1;end};end
Scope2C.define_method(:make,Scope2D::Scope2BODY);p Scope2C.new.make;p [Scope2C.method_defined?(:x),Scope2D.method_defined?(:x)]

# nested-dm-eval
class Scope3C;end;class Scope3D;end
body=Scope3D.class_eval {proc {def x;1;end}}
Scope3C.define_method(:make,body);p Scope3C.new.make;p [Scope3C.method_defined?(:x),Scope3D.method_defined?(:x),Object.method_defined?(:x)]

# dm-super
class Scope4B;def x;[:base];end;end
class Scope4C<Scope4B;define_method(:x){super()+[:child]};end;p Scope4C.new.x

# dm-single-vis-shared
class Scope5C;end;class Scope5D;Scope5BODY=proc {private;def x;1;end};Scope5C.define_singleton_method(:change,Scope5BODY);Scope5C.change;def y;2;end;end;p [Scope5D.private_method_defined?(:x),Scope5D.private_method_defined?(:y),Scope5C.method_defined?(:x)]
