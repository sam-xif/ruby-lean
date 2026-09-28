puts "clone-string-hook"
begin
  class SL298Case6<String;
  def initialize_clone(other,freeze:nil);
  @f=freeze;
  super;
  end;
  attr_reader :f;
  end;
  s=SL298Case6.new("abc").freeze;
  t=s.clone(freeze:false);
  p [t.class,t.f,t.frozen?]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-options"
begin
  class CL298Case16;
  def initialize_clone(o,**kw);
  p [frozen?,o.frozen?,kw,block_given?];
  @x=1;
  super;
  :ignored;
  end;
  attr_reader :x;
  end;
  o=CL298Case16.new.freeze;
  [{}, {freeze:nil},{freeze:false},{freeze:true}].each{|kw|c=o.clone(**kw){:bad};
  p [c.x,c.frozen?,c.equal?(o)]}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-observes-string"
begin
  class SL298Case17<String;
  def initialize_clone(o,**kw);
  p [self,instance_variables,frozen?];
  super;
  p self;
  end;
  end;
  o=SL298Case17.new("abc");
  o.instance_variable_set(:@x,1);
  p o.clone
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-skips-super"
begin
  class SL298Case18<String;
  def initialize_clone(o,**kw);
  self << "hook";
  end;
  end;
  o=SL298Case18.new("abc");
  p [o.clone,o.clone(freeze:true)]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-copy"
begin
  class SL298Case19<String;
  def initialize_copy(o);
  p [:copy,self];
  super;
  self << "copy";
  :ignored;
  end;
  end;
  o=SL298Case19.new("abc").freeze;
  p o.clone(freeze:false)
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-mutate-original"
begin
  class SL298Case20<String;
  def initialize_clone(o,**kw);
  o << "changed";
  super;
  end;
  end;
  o=SL298Case20.new("abc");
  p [o.clone,o]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-original-freeze-in-hook"
begin
  class CL298Case21;
  def initialize_clone(o,**kw);
  o.freeze;
  super;
  end;
  end;
  [nil,false,true].each{|f|o=CL298Case21.new;
  c=o.clone(freeze:f);
  p [o.frozen?,c.frozen?]}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-copy-freeze-in-hook"
begin
  class CL298Case22;
  def initialize_clone(o,**kw);
  freeze;
  end;
  end;
  [nil,false,true].each{|f|c=CL298Case22.new.clone(freeze:f);
  p [f,c.frozen?]}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-raise"
begin
  class CL298Case23;
  def initialize_clone(o,**kw);
  $copy=self;
  @x=7;
  raise "hook";
  end;
  attr_reader :x;
  end;
  o=CL298Case23.new.freeze;
  begin;
  o.clone(freeze:true);
  rescue=>e;
  p [e.message,$copy.frozen?,$copy.x];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-throw"
begin
  class CL298Case24;
  def initialize_clone(o,**kw);
  $copy=self;
  throw :done,:hook;
  end;
  end;
  o=CL298Case24.new.freeze;
  p catch(:done){o.clone(freeze:true)};
  p $copy.frozen?
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-exception-hook"
begin
  class EL298Case31<StandardError;
  def initialize_clone(o,**kw);
  p [message,instance_variables,frozen?];
  super;
  p message;
  end;
  end;
  e=EL298Case31.new("x");
  e.instance_variable_set(:@x,1);
  p e.clone.message
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-source-ivars-during-hook"
begin
  class CL298Case32;
  def initialize_clone(o,**kw);
  o.instance_variable_set(:@x,2);
  p [@x,o.instance_variable_get(:@x)];
  super;
  p @x;
  end;
  end;
  o=CL298Case32.new;
  o.instance_variable_set(:@x,1);
  o.clone;
  nil
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-undef-hook"
begin
  class CL298Case35;
  undef initialize_clone;
  def method_missing(n,*a,**kw);
  p [n,a.length,kw];
  :ignored;
  end;
  end;
  c=CL298Case35.new.freeze;
  p c.clone(freeze:false).frozen?
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-array-shell"
begin
  class AL298Case36<Array;
  def initialize_clone(o,**kw);
  p [self,instance_variables,frozen?];
  super;
  p self;
  end;
  end;
  a=AL298Case36.new;
  a<<1;
  a.instance_variable_set(:@x,7);
  p a.clone(freeze:false)
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hash-shell"
begin
  class HL298Case37<Hash;
  def initialize_clone(o,**kw);
  p [self,self[:absent],instance_variables,frozen?];
  super;
  p [self,self[:absent]];
  end;
  end;
  h=HL298Case37.new(9);
  h[:a]=1;
  h.instance_variable_set(:@x,7);
  p h.clone(freeze:true)
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hook-prepend"
begin
  module M;
  def initialize_clone(o,**kw);
  p [:before,kw];
  super;
  p :after;
  end;
  end;
  class CL298Case55;
  prepend M;
  end;
  p CL298Case55.new.clone(freeze:true).frozen?
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-copy-hook-undef"
begin
  class CL298Case57;
  undef initialize_copy;
  def method_missing(n,*a);
  p [n,a.length];
  :hook;
  end;
  end;
  p CL298Case57.new.clone(freeze:true).frozen?
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

nil
