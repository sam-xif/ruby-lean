class Module;def self.to_s;p :effect;"FAKE";end;end;module M;end;begin;Class.new(M);rescue=>e;p [e.class,e.message];end;begin;class C<M;end;rescue=>e;p [e.class,e.message];end
