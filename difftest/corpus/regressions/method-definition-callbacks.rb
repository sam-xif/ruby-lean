# L282: method definition callbacks.

# define-alias
module Case0
  class C
   def self.method_added(n);p [:added,n,method_defined?(n)];end
   def x;1;end
   p alias_method(:y,:x)
   alias z x
   p define_method(:v){2}
   p attr_accessor(:a,'b')
  end
  p [C.new.y,C.new.z,C.new.v]
end

# single
module Case1
  o=Object.new
  def o.singleton_method_added(n);p [:added,n];end
  def o.a;1;end
  p o.define_singleton_method(:b){2}
  class<<o
   alias c a
   p attr_reader(:x)
  end
  p [o.a,o.b,o.c]
end

# hook-super
module Case2
  class C
   def self.method_added(n);p n;super;end
   def x;end
  end
end

# hook-private
module Case3
  class C
   class << self
   private
   def method_added(n);p n;end
   end
   def x;end
  end
end

# hook-missing
module Case4
  class C
   class << self;undef method_added;end
   def self.method_missing(n,*a);p [n,a];end
   def x;end
  end
end

# hook-raise
module Case5
  class C
   def self.method_added(n);raise 'defined';end
  end
  begin;C.define_method(:x){3};rescue=>e;p e.message;end
  p C.new.x
end

# module-function
module Case6
  module M
   def self.singleton_method_added(n);p [:single,n];end
   def a;1;end;def b;2;end
   p module_function(:a,:b)
  end
  p [M.a,M.b,M.private_method_defined?(:a)]
end

# singleton-copy
module Case7
  class C
   def self.singleton_method_added(n);p n;end
   def self.x;1;end
   class << self;alias y x;end
  end
  p C.y
end
