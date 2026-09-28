puts "constant-rescue-target"
begin
  module ML292Case16;
  def self.const_added(n);
  p n;
  end;
  begin;
  raise "x";
  rescue=>EL292Case16;
  p EL292Case16.message;
  end;
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-rescue-namespace"
begin
  module ML292Case30;
  def self.const_added(n);
  p [n,const_get(n,false).equal?($!),$!.message];
  end;
  begin;
  raise "x";
  rescue=>EL292Case30;
  p [EL292Case30.message,self.const_defined?(:EL292Case30,false)];
  end;
  end;
  p [ML292Case30::EL292Case30.message,Object.const_defined?(:EL292Case30,false)]
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-rescue-hook-raises"
begin
  module ML292Case31;
  def self.const_added(n);
  raise "hook";
  end;
  begin;
  begin;
  raise "original";
  rescue=>EL292Case31;
  p :wrong;
  ensure;
  p [:ensure,$!.message];
  end;
  rescue=>e;
  p [e.message,EL292Case31.message];
  end;
  end;
  p $!
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-rescue-frozen"
begin
  module ML292Case32;
  freeze;
  begin;
  begin;
  raise "original";
  rescue=>EL292Case32;
  p :wrong;
  ensure;
  p :ensure;
  end;
  rescue=>e;
  p [e.class,e.message,const_defined?(:EL292Case32,false)];
  end;
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

puts "constant-rescue-retry"
begin
  module ML292Case33;
  @n=0;
  def self.const_added(n);
  p [:hook,n];
  end;
  begin;
  @n+=1;
  raise "x" if @n<3;
  rescue=>EL292Case33;
  retry;
  end;
  p [@n,EL292Case33.message];
  end
rescue Exception => __l292_error
  p [:caught, __l292_error.class, __l292_error.message]
end

nil
