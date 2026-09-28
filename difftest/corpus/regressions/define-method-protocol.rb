# L283: define method protocol.

# dm-argument-body
class Scope1C;end;[[],[:x],[:x,1],[:x,proc{1},3]].each do |a|;begin;Scope1C.define_method(*a);rescue=>e;p [e.class,e.message];end;end;Scope1C.define_method(:x,proc{1}){2};p Scope1C.new.x

# dm-wrong-receiver
o=Object.new;begin;o.define_method;rescue=>e;p [e.class,e.message];end;begin;o.private;rescue=>e;p [e.class,e.message];end

# dm-vis-shared
class Scope3C;end
class Scope3D
 Scope3BODY=proc {private;def x;1;end}
 Scope3C.define_method(:make,Scope3BODY)
 Scope3C.new.make
 def y;2;end
end
p [Scope3D.private_method_defined?(:x),Scope3D.private_method_defined?(:y)]
