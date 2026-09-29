puts "dup-hooks"
begin
  class CL299Case1;
  def initialize_dup(o);
  p [:dup,frozen?,o.frozen?,block_given?];
  @x=1;
  super;
  :ignored;
  end;
  def initialize_copy(o);
  p :copy;
  super;
  end;
  attr_reader :x;
  end;
  o=CL299Case1.new.freeze;
  c=o.dup{raise "wrong"};
  p [c.x,c.frozen?,c.equal?(o)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-string-shell"
begin
  class SL299Case3<String;
  def initialize_dup(o);
  p [self,encoding.name,instance_variables,frozen?];
  super;
  p [self,encoding.name];
  end;
  end;
  o=SL299Case3.new("é");
  o.instance_variable_set(:@x,1);
  p o.freeze.dup
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-array-shell"
begin
  class AL299Case5<Array;
  def initialize_dup(o);
  p [self,instance_variables,frozen?];
  super;
  p self;
  end;
  end;
  a=AL299Case5.new;
  a<<1;
  a.instance_variable_set(:@x,1);
  p a.freeze.dup
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-hash-shell"
begin
  class HL299Case6<Hash;
  def initialize_dup(o);
  p [self,self[:missing],instance_variables];
  super;
  p [self,self[:missing]];
  end;
  end;
  h=HL299Case6.new(9);
  h[:a]=1;
  h.instance_variable_set(:@x,1);
  p h.freeze.dup
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-exception-shell"
begin
  class EL299Case7<StandardError;
  def initialize_dup(o);
  p [message,instance_variables,frozen?];
  super;
  end;
  end;
  e=EL299Case7.new("x");
  e.instance_variable_set(:@x,1);
  p e.freeze.dup.message
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-skip-super"
begin
  class SL299Case8<String;
  def initialize_dup(o);
  self << "hook";
  end;
  end;
  p SL299Case8.new("original").dup
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-copy-hook"
begin
  class SL299Case9<String;
  def initialize_copy(o);
  p self;
  super;
  self << "copy";
  :ignored;
  end;
  end;
  p SL299Case9.new("original").dup
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-source-freeze"
begin
  class CL299Case11;
  def initialize_dup(o);
  o.freeze;
  super;
  end;
  end;
  o=CL299Case11.new;
  c=o.dup;
  p [o.frozen?,c.frozen?]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-copy-freeze"
begin
  class CL299Case12;
  def initialize_dup(o);
  freeze;
  :ignored;
  end;
  end;
  o=CL299Case12.new;
  c=o.dup;
  p [o.frozen?,c.frozen?]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-hook-raise"
begin
  class CL299Case13;
  def initialize_dup(o);
  $copy=self;
  @x=7;
  raise "hook";
  end;
  attr_reader :x;
  end;
  begin;
  CL299Case13.new.freeze.dup;
  rescue=>e;
  p [e.message,$copy.x,$copy.frozen?];
  end
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-hook-throw"
begin
  class CL299Case14;
  def initialize_dup(o);
  $copy=self;
  throw :done,:hook;
  end;
  end;
  p catch(:done){CL299Case14.new.freeze.dup};
  p $copy.frozen?
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-alias"
begin
  class CL299Case15;
  alias native_dup dup;
  def dup;
  :override;
  end;
  def initialize_dup(o);
  @x=7;
  super;
  end;
  attr_reader :x;
  end;
  c=CL299Case15.new;
  p [c.dup,c.native_dup.x]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-super"
begin
  class SL299Case16<String;
  def dup;
  super;
  end;
  def initialize_dup(o);
  super;
  self << "copy";
  end;
  end;
  p SL299Case16.new("x").dup
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-native-hook-alias"
begin
  class CL299Case30;
  alias native_init initialize_dup;
  def initialize_dup(o);
  native_init(o);
  @x=7;
  end;
  attr_reader :x;
  end;
  p CL299Case30.new.dup.x
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-prepend"
begin
  module ML299Case31;
  def initialize_dup(o);
  p :before;
  super;
  p :after;
  end;
  end;
  class CL299Case31;
  prepend ML299Case31;
  end;
  p CL299Case31.new.dup.class
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-missing-hook"
begin
  class CL299Case32;
  undef initialize_dup;
  def method_missing(n,*a,**kw);
  p [n,a.length,kw];
  :ignored;
  end;
  end;
  p CL299Case32.new.freeze.dup.frozen?
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-missing-copy-hook"
begin
  class CL299Case33;
  undef initialize_copy;
  def method_missing(n,*a);
  p [n,a.length];
  :ignored;
  end;
  end;
  p CL299Case33.new.dup.class
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

nil
