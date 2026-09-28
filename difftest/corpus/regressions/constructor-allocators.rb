# allocator-core
[Integer,Float,Symbol,NilClass,TrueClass,FalseClass,Rational,Complex,Proc].each{|k|p [k,k.respond_to?(:new),k.respond_to?(:new,true),k.respond_to?(:allocate)];begin;k.new;rescue=>e;p [e.class,e.message];end;begin;k.allocate;rescue=>e;p [e.class,e.message];end}

# allocator-integer
begin;Integer.new;rescue=>e;p [e.class,e.message];end;class CPart1<Integer;end;begin;CPart1.new;rescue=>e;p [e.class,e.message];end

nil
