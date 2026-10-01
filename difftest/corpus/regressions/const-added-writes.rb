puts "constant-writes"
begin
  module ML292Case1;
  def self.const_added(n);
  p [n,const_get(n,false)];
  7;
  end;
  XL292Case1=1;
  XL292Case1=2;
  end;
  p ML292Case1.const_set(:YL292Case1,3);
  ML292Case1::YL292Case1=4;
  p [ML292Case1::XL292Case1,ML292Case1::YL292Case1]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-super-private"
begin
  module ML292Case2;
  class<<self;
  private;
  def const_added(n);
  p [:hook,n,super(n)];
  end;
  end;
  XL292Case2=1;
  end;
  p ML292Case2.const_set(:YL292Case2,2)
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-default-arity"
begin
  p Module.send(:const_added,7);
  begin;
  Module.send(:const_added);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  Module.send(:const_added,1,2);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-recursive-hook"
begin
  module ML292Case5;
  def self.const_added(n);
  p n;
  const_set(:YL292Case5,2) if n==:XL292Case5;
  end;
  XL292Case5=1;
  end;
  p [ML292Case5::XL292Case5,ML292Case5::YL292Case5]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-name-before-hook"
begin
  module ML292Case9;
  def self.const_added(n);
  p const_get(n,false).name;
  end;
  end;
  c=Class.new;
  m=Module.new;
  p ML292Case9.const_set(:CL292Case9,c).equal?(c);
  ML292Case9::N=m;
  p [c.name,m.name]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-lexical-hook"
begin
  module AL292Case15;
  def self.const_added(n);
  p [:AL292Case15,n];
  end;
  module BL292Case15;
  def self.const_added(n);
  p [:BL292Case15,n];
  end;
  XL292Case15=1;
  end;
  end;
  AL292Case15::BL292Case15::YL292Case15=2;
  p [AL292Case15::BL292Case15::XL292Case15,AL292Case15::BL292Case15::YL292Case15]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-hook-overrides"
begin
  module ML292Case26;
  class<<self;
  alias saved const_added;
  def const_added(n);
  p saved(n);
  end;
  end;
  XL292Case26=1;
  end;
  p ML292Case26::XL292Case26
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-private-reassignment"
begin
  module ML292Case29;
  XL292Case29=1;
  private_constant :XL292Case29;
  def self.const_added(n);
  p [n,const_get(n,false)];
  end;
  XL292Case29=2;
  end;
  begin;
  p ML292Case29::XL292Case29;
  rescue=>e;
  p [e.class,e.message];
  end;
  p ML292Case29.const_get(:XL292Case29,false)
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-default-binary-runtime"
begin
  p Module.send(:const_added,255.chr)
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-default-private"
begin
  begin;
  Module.const_added(:XL292Case39);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

nil
