puts "class-new-inherited"
begin
  class PL291Case1;
  def self.inherited(c);
  p [:inherited,c.superclass==self,c.name];
  end;
  end;
  c=Class.new(PL291Case1){p :body};
  p c.superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-stmt-inherited"
begin
  class PL291Case2;
  def self.inherited(c);
  p [:inherited,c.superclass==self,c.name,defined?(CL291Case2)];
  end;
  end;
  class CL291Case2<PL291Case2;
  p :body;
  end;
  p CL291Case2.superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-reopen"
begin
  class PL291Case5;
  def self.inherited(c);
  p :inherited;
  end;
  end;
  class CL291Case5<PL291Case5;
  p :first;
  end;
  class CL291Case5;
  p :second;
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-undef"
begin
  class PL291Case14;
  class<<self;
  undef inherited;
  end;
  def self.method_missing(*a);
  p a[0];
  end;
  end;
  c=Class.new(PL291Case14);
  p c.superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-private"
begin
  class PL291Case15;
  class<<self;
  private;
  def inherited(c);
  p :private_hook;
  end;
  end;
  end;
  class CL291Case15<PL291Case15;
  end;
  p CL291Case15.superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-super"
begin
  class PL291Case16;
  def self.inherited(c);
  p [:hook,super];
  end;
  end;
  p Class.new(PL291Case16).superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-mutation"
begin
  class PL291Case28;
  def self.inherited(c);
  def c.ready;
  true;
  end;
  c.class_eval{def x;
  3;
  end};
  end;
  end;
  class CL291Case28<PL291Case28;
  p [ready,new.x];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-super-alias"
begin
  class PL291Case29;
  class<<self;
  alias saved inherited;
  def inherited(c);
  p saved(c);
  end;
  end;
  end;
  p Class.new(PL291Case29).superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-raise-retain"
begin
  $c=nil;
  class PL291Case30;
  def self.inherited(c);
  $c=c;
  raise "halt";
  end;
  end;
  begin;
  Class.new(PL291Case30);
  rescue;
  p $c.superclass;
  begin;
  $c.send(:initialize);
  rescue=>e;
  p e.message;
  end;
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-hook-replaces-binding"
begin
  class PL291Case38;
  def self.inherited(c);
  Object.const_set(:CL291Case38,7);
  end;
  end;
  v=class CL291Case38<PL291Case38;
  def self.x;
  8;
  end;
  self;
  end;
  p [CL291Case38,v.x,v.superclass]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-uninitialized-reopen"
begin
  CL291Case42=Class.allocate;
  class CL291Case42;
  def x;
  1;
  end;
  end;
  begin;
  CL291Case42.superclass;
  rescue=>e;
  p e.message;
  end;
  CL291Case42.send(:initialize);
  p CL291Case42.new.x
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-inherited-arity"
begin
  p Class.send(:inherited,nil);
  begin;
  Class.send(:inherited);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  Class.send(:inherited,1,2);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-constant-assignment-in-hook"
begin
  class PL291Case48;
  def self.inherited(c);
  Object.const_set(:SavedL291Case48,c);
  p c.name;
  end;
  end;
  CL291Case48=Class.new(PL291Case48){p name};
  p [CL291Case48.name,SavedL291Case48.equal?(CL291Case48)]
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

nil
