puts "constant-missing-hook"
begin
  module ML292Case3;
  class<<self;
  undef const_added;
  def method_missing(n,*a);
  p [n,a];
  end;
  end;
  XL292Case3=1;
  end;
  p ML292Case3::XL292Case3
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-hook-raise"
begin
  module ML292Case6;
  def self.const_added(n);
  p [:hook,n];
  raise "stop";
  end;
  end;
  begin;
  ML292Case6::XL292Case6=1;
  rescue=>e;
  p [e.message,ML292Case6::XL292Case6];
  end;
  begin;
  ML292Case6.const_set(:YL292Case6,2);
  rescue=>e;
  p [e.message,ML292Case6::YL292Case6];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-hook-throw"
begin
  module ML292Case7;
  def self.const_added(n);
  throw :done,n;
  end;
  end;
  p catch(:done){ML292Case7::XL292Case7=7;
  :wrong};
  p ML292Case7::XL292Case7
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-hook-freeze"
begin
  module ML292Case8;
  def self.const_added(n);
  freeze;
  end;
  end;
  p ML292Case8.const_set(:XL292Case8,1);
  begin;
  ML292Case8::YL292Case8=2;
  rescue=>e;
  p [e.class,e.message];
  end;
  p [ML292Case8::XL292Case8,ML292Case8.const_defined?(:YL292Case8,false)]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "raise-keeps-name"
begin
  module ML292Case19;
  def self.const_added(n);
  raise "stop";
  end;
  end;
  c=Class.new;
  begin;
  ML292Case19.const_set(:CL292Case19,c);
  rescue=>e;
  p [e.message,c.name,ML292Case19::CL292Case19.equal?(c)];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-no-hook-method"
begin
  module ML292Case27;
  class<<self;
  undef const_added;
  end;
  end;
  begin;
  ML292Case27::XL292Case27=1;
  rescue=>e;
  p [e.class,e.message,ML292Case27::XL292Case27];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-hook-ensures"
begin
  module ML292Case28;
  def self.const_added(n);
  p [:hook,n];
  raise "x";
  ensure;
  p :inner;
  end;
  end;
  begin;
  ML292Case28::XL292Case28=1;
  rescue=>e;
  p e.message;
  ensure;
  p :outer;
  end;
  p ML292Case28::XL292Case28
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-hook-missing-fallback"
begin
  module ML292Case36;
  class<<self;
  undef const_added;
  def method_missing(n,*a);
  p [n,a];
  super;
  end;
  end;
  end;
  begin;
  ML292Case36.const_set(:XL292Case36,2);
  rescue=>e;
  p [e.class,e.message,ML292Case36::XL292Case36];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

nil
