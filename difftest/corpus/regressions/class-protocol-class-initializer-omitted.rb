class Class;def initialize(*a);p a;end;end;c=Class.new(Array);p [c.class,c.name];begin;c.superclass;rescue=>e;p [e.class,e.message];end
