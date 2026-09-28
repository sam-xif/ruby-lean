class TrueClass;class<<self;undef to_s;def method_missing(n,*a);p n;"MISSING";end;end;end;begin;Class.new(true);rescue=>e;p [e.class,e.message];end
