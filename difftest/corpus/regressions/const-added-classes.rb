puts "class-hook-order"
begin
  class PL292Case10;
  def self.inherited(c);
  p [:inherited,c.name];
  end;
  def self.parent;
  3;
  end;
  end;
  module ML292Case10;
  def self.const_added(n);
  v=const_get(n,false);
  p [:constant,n,v.name,v.superclass,v.parent];
  end;
  class CL292Case10<PL292Case10;
  p [:body,self];
  end;
  end;
  p ML292Case10::CL292Case10.superclass
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-eval-lexical-binding"
begin
  class PL292Case11;
  def self.inherited(c);
  p :wrong_inherited;
  end;
  end;
  module ML292Case11;
  def self.const_added(n);
  p n;
  raise "stop";
  end;
  end;
  begin;
  ML292Case11.module_eval {class CL292Case11<PL292Case11;
  puts :wrong_body;
  end};
  rescue=>e;
  p [e.message,ML292Case11::CL292Case11.superclass];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-hook-replaces-binding"
begin
  class PL292Case12;
  def self.inherited(c);
  p [:inherited,c.name];
  end;
  end;
  module ML292Case12;
  def self.const_added(n);
  v=const_get(n,false);
  p [:constant,n,v];
  const_set(n,7) if v.is_a?(Class);
  end;
  class CL292Case12<PL292Case12;
  p [:body,self,superclass];
  end;
  end;
  p ML292Case12::CL292Case12
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-scoped-hook"
begin
  module ML292Case13;
  def self.const_added(n);
  p [n,const_get(n,false).name];
  end;
  end;
  class ML292Case13::CL292Case13;
  p :body;
  end;
  class ML292Case13::CL292Case13;
  p :reopen;
  end;
  module ML292Case13::N;
  p :module;
  end;
  module ML292Case13::N;
  p :reopen_module;
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-class-new-order"
begin
  module ML292Case17;
  def self.const_added(n);
  p [:constant,n];
  end;
  end;
  class PL292Case17;
  def self.inherited(c);
  p [:inherited,c.name];
  end;
  end;
  ML292Case17::CL292Case17=Class.new(PL292Case17){p [:body,name]};
  p ML292Case17::CL292Case17.name
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-hook-raise"
begin
  class PL292Case18;
  def self.inherited(c);
  p :wrong_inherited;
  end;
  end;
  module ML292Case18;
  def self.const_added(n);
  p n;
  raise "stop";
  end;
  end;
  begin;
  module ML292Case18;
  class CL292Case18<PL292Case18;
  puts :wrong_body;
  end;
  end;
  rescue=>e;
  p [e.message,ML292Case18::CL292Case18.superclass];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-const-hook-throw"
begin
  module ML292Case20;
  def self.const_added(n);
  throw :done,n;
  end;
  end;
  p catch(:done){class ML292Case20::CL292Case20;
  puts :wrong;
  end};
  p ML292Case20::CL292Case20.name
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-hook-freezes-class"
begin
  module ML292Case21;
  def self.const_added(n);
  const_get(n,false).freeze;
  end;
  end;
  begin;
  class ML292Case21::CL292Case21;
  p :body;
  def x;
  1;
  end;
  end;
  rescue=>e;
  p [e.class,e.message,ML292Case21::CL292Case21.frozen?];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-hook-freezes-namespace"
begin
  module ML292Case22;
  def self.const_added(n);
  freeze;
  end;
  end;
  class ML292Case22::CL292Case22;
  def x;
  3;
  end;
  end;
  p [ML292Case22.frozen?,ML292Case22::CL292Case22.new.x]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "class-const-hook-changes-inherited"
begin
  class PL292Case23;
  end;
  module ML292Case23;
  def self.const_added(n);
  def PL292Case23.inherited(c);
  p [:late,c.name];
  end;
  end;
  class CL292Case23<PL292Case23;
  p :body;
  end;
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-subclass-hook"
begin
  class PL292Case25;
  def self.const_added(n);
  p [self,n];
  end;
  end;
  class CL292Case25<PL292Case25;
  XL292Case25=1;
  end;
  PL292Case25::YL292Case25=2;
  CL292Case25::YL292Case25=3;
  p [PL292Case25::YL292Case25,CL292Case25::YL292Case25]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "module-subclass-hook"
begin
  class MCL292Case35<Module;
  def const_added(n);
  p [n,name];
  end;
  end;
  ML292Case35=MCL292Case35.new;
  ML292Case35::XL292Case35=1;
  p ML292Case35::XL292Case35
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-class-block-order"
begin
  module ML292Case37;
  def self.const_added(n);
  p [:bound,n,const_get(n,false).name];
  end;
  end;
  ML292Case37::CL292Case37=Class.new{p [:body,name]};
  p ML292Case37::CL292Case37.name
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

nil
