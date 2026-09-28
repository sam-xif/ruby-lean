# L282: constant mutation.

# constant-freeze
module Case0
  class C;X=1;end;C.freeze;begin;C.const_set(:Y,2);rescue=>e;p [e.class,e.message];end;begin;C::Z=3;rescue=>e;p [e.class,e.message];end
end

# constant-visibility
module Case1
  module C;X=1;end;p C.private_constant(:X);p C.public_constant(:X);begin;C.private_constant(:X,:Missing);rescue=>e;p e.message;end;begin;p C::X;rescue=>e;p e.message;end;C.freeze;begin;C.public_constant(:X);rescue=>e;p e.message;end
end
