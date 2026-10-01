puts "constant-set-arity"
begin
  [[],[:XL294Case4],[:XL294Case4,1,2]].each{|a|begin;
  Module.const_set(*a);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-keywords"
begin
  m=Module.new;
  p m.const_set(:XL294Case5,x:1);
  p m.const_get(:XL294Case5)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-alias"
begin
  module ML294Case6;
  class<<self;
  alias put const_set;
  def const_added(n);
  p n;
  end;
  end;
  end;
  p ML294Case6.put(:XL294Case6,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-super"
begin
  class MCL294Case7<Module;
  def const_set(*a);
  p :before;
  p super;
  end;
  end;
  m=MCL294Case7.new;
  m.const_set(:XL294Case7,1);
  p m.const_get(:XL294Case7)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-override"
begin
  module ML294Case8;
  def self.const_set(*a);
  p a;
  :custom;
  end;
  end;
  p ML294Case8.const_set(:XL294Case8,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-undef"
begin
  module ML294Case9;
  class<<self;
  undef const_set;
  def method_missing(n,*a);
  p [n,a];
  end;
  end;
  end;
  p ML294Case9.const_set(:XL294Case9,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-private"
begin
  module ML294Case45;
  private_class_method :const_set;
  end;
  begin;
  ML294Case45.const_set(:XL294Case45,1);
  rescue=>e;
  p [e.class,e.message];
  end;
  p ML294Case45.send(:const_set,:XL294Case45,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-set-alias-snapshot"
begin
  module ML294Case46;
  class<<self;
  alias put const_set;
  def const_set(*a);
  :new;
  end;
  end;
  end;
  p ML294Case46.put(:XL294Case46,1);
  p ML294Case46::XL294Case46;
  p ML294Case46.const_set(:YL294Case46,2)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-empty-keywords"
begin
  m=Module.new;
  p m.const_set(:XL294Case47,1,**{});
  p m.const_get(:XL294Case47)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-extra-keywords"
begin
  begin;
  Module.new.const_set(:XL294Case48,1,x:2);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

nil
