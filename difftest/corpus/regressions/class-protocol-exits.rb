puts "class-new-inherited-raises"
begin
  class PL291Case3;
  def self.inherited(c);
  p :inherited;
  raise "stop";
  end;
  end;
  begin;
  CL291Case3=Class.new(PL291Case3){p :wrong};
  rescue=>e;
  p [e.class,e.message,defined?(CL291Case3)];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-stmt-inherited-raises"
begin
  class PL291Case4;
  def self.inherited(c);
  p :inherited;
  raise "stop";
  end;
  end;
  begin;
  class CL291Case4<PL291Case4;
  p :wrong;
  end;
  rescue=>e;
  p [e.class,e.message,defined?(CL291Case4),CL291Case4.superclass];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-freeze"
begin
  class PL291Case31;
  def self.inherited(c);
  c.freeze;
  end;
  end;
  begin;
  Class.new(PL291Case31){p :body;
  def x;
  1;
  end};
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-block-break"
begin
  p(Class.new{break 7});
  p(Module.new{break 8});
  c=Class.allocate;
  p(c.send(:initialize){break 9});
  p c.superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-block-next"
begin
  p Class.new{next 7}.class;
  p Module.new{next 8}.class;
  c=Class.allocate;
  p c.send(:initialize){next 9}.equal?(c)
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-hook-ensure"
begin
  class PL291Case46;
  def self.inherited(c);
  p :hook;
  raise "stop";
  ensure;
  p :hook_ensure;
  end;
  end;
  begin;
  class CL291Case46<PL291Case46;
  p :wrong;
  end;
  rescue=>e;
  p [e.message,CL291Case46.superclass];
  ensure;
  p :outer_ensure;
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

nil
