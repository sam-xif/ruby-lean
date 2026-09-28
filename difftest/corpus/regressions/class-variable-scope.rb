# L283: class variable scope.

# class-variable-lexical
class Scope1C;@@x=2;class<<self;def x;@@x;end;end;end;p Scope1C.x;class<<Scope1C;def outside;@@x;end;end;begin;p Scope1C.outside;rescue=>e;p [e.class,e.message];end;module Scope1O;@@y=4;class Scope1C;end;class<<Scope1C;def y;@@y;end;end;end;p Scope1O::Scope1C.y;class Scope1A;def self.eval_other(c);c.class_eval {@@z=5};end;def self.z;@@z;end;end;class Scope1B;end;Scope1A.eval_other(Scope1B);p Scope1A.z

# class-variable-toplevel
class Object;@@global_scope=3;end;p defined?(@@global_scope);begin;proc{p @@global_scope}.call;rescue=>e;p [e.class,e.message];end;def outside_cvar;@@global_scope;end;begin;p outside_cvar;rescue=>e;p [e.class,e.message];end;begin;proc{@@fresh_scope=(p :rhs;4)}.call;rescue=>e;p [e.class,e.message];end;p defined?(@@fresh_scope)
