puts "class-new-module"
begin
  module ML291Case7;
  end;
  begin;
  p Class.new(ML291Case7);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-native-initialize"
begin
  m=Module.new;
  p m.send(:initialize){p :body}.equal?(m);
  p m.class
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-eigen-rewire"
begin
  c=Class.allocate;
  e=c.singleton_class;
  def c.mine;
  7;
  end;
  class PL291Case23;
  def self.parent;
  8;
  end;
  end;
  c.send(:initialize,PL291Case23);
  p [c.singleton_class.equal?(e),c.parent,c.mine,c.singleton_class.superclass.equal?(PL291Case23.singleton_class)]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-allocate"
begin
  m=Module.allocate;
  p [m.class,m.name,m.send(:initialize)];
  p m.send(:initialize){p :body}
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-reinitialize-frozen"
begin
  m=Module.new.freeze;
  p m.send(:initialize){p :body};
  begin;
  m.send(:initialize,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-subclass-implicit-block"
begin
  class ML291Case37<Module;
  def initialize(x);
  p x;
  super();
  end;
  end;
  m=ML291Case37.new(7){|v|p [self.equal?(v),self.class];
  def x;
  9;
  end};
  c=Class.new{include m};
  p [c.new.x,m.singleton_class.superclass==ML291Case37]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-replaces-old-eigen"
begin
  c=Class.allocate;
  e=c.singleton_class;
  def c.mine;
  7;
  end;
  c.send(:initialize);
  p [c.singleton_class.equal?(e),c.respond_to?(:mine),e.superclass]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-subclass-repr"
begin
  class ML291Case54<Module;
  end;
  m=ML291Case54.new;
  p [m,m.to_s,m.name,m.class];
  e=m.singleton_class;
  p [m,m.to_s,e,e.superclass];
  EL291Case54=e;
  p [m,m.to_s,e,e.name]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-subclass-anonymous-repr"
begin
  m=Class.new(Module).new;
  p [m,m.to_s,m.class];
  p [m,m.to_s,m.singleton_class];
  p m.to_s
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-subclass-frozen-repr"
begin
  class ML291Case56<Module;
  end;
  m=ML291Case56.new.freeze;
  p m.to_s;
  p [m.singleton_class,m.to_s,m.name];
  ML291Case56::SavedL291Case56=m;
  p [m,m.name,m.singleton_class]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "module-base-repr"
begin
  m=Module.new;
  p [m,m.to_s,m.singleton_class,m];
  c=Class.new;
  p [c,c.to_s,c.singleton_class,c];
  EL291Case57=m.singleton_class;
  p [m,m.singleton_class,EL291Case57.name]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

nil
