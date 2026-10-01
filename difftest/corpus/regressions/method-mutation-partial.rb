# L282: method mutation partial.

# remove-undef
module Case0
  class C
   def a;1;end;def b;2;end
   def self.method_removed(n);p [:removed,n,method_defined?(n)];end
   def self.method_undefined(n);p [:undefined,n,method_defined?(n)];end
   p remove_method(:a)
   undef b
  end
end

# remove-partial
module Case1
  class C
   def a;end;def b;end
   def self.method_removed(n);p [n,method_defined?(:b)];raise 'stop';end
  end
  begin;C.send(:remove_method,:a,:b);rescue=>e;p e.message;end
  p [C.method_defined?(:a),C.method_defined?(:b)]
end

# attrs-partial
module Case2
  class C
   def self.method_added(n)
   p [n,method_defined?(:x=),method_defined?(:y)]
   raise 'stop' if n==:x=
   end
  end
  begin;C.attr_accessor(:x,:y);rescue=>e;p e.message;end
  p [C.method_defined?(:x),C.method_defined?(:x=),C.method_defined?(:y)]
end

# attrs-freeze
module Case3
  class C
   def self.method_added(n);freeze if n==:x;end
  end
  begin;C.attr_accessor(:x);rescue=>e;p [e.class,e.message];end
  p [C.method_defined?(:x),C.method_defined?(:x=)]
end

# hook-mutates-next
module Case4
  class C
   def a;end;def b;end
   def self.method_removed(n);undef_method(:b) if n==:a;end
  end
  begin;C.send(:remove_method,:a,:b);rescue=>e;p e.message;end
  p [C.method_defined?(:a),C.method_defined?(:b)]
end

# single-remove
module Case5
  o=Object.new
  def o.a;end;def o.b;end
  def o.singleton_method_removed(n);p [:removed,n];end
  def o.singleton_method_undefined(n);p [:undefined,n];end
  class<<o;remove_method(:a);undef b;end
end
