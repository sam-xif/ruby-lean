puts "dup-singleton-methods"
begin
  o=Object.new;
  def o.tag;
  7;
  end;
  o.instance_variable_set(:@x,1);
  c=o.freeze.dup;
  p [c.class,c.frozen?,c.respond_to?(:tag),c.instance_variable_get(:@x)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-singleton-hooks-ignored"
begin
  o="abc";
  def o.initialize_dup(x);
  raise "wrong";
  end;
  def o.initialize_copy(x);
  raise "wrong";
  end;
  c=o.dup;
  p [c,c.frozen?]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-extend-ignored"
begin
  module ML299Case19;
  def tag;
  7;
  end;
  def initialize_dup(o);
  raise "wrong";
  end;
  end;
  class CL299Case19;
  def initialize_dup(o);
  p :class;
  super;
  end;
  end;
  o=CL299Case19.new;
  o.extend ML299Case19;
  c=o.dup;
  p [c.class,c.respond_to?(:tag)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-singleton-undef-ignored"
begin
  o=Object.new;
  class<<o;
  undef initialize_dup;
  undef initialize_copy;
  end;
  c=o.dup;
  p [c.class,c.equal?(o)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-singleton-on-binary"
begin
  s=255.chr;
  def s.tag;
  7;
  end;
  t=s.dup;
  p [t.bytes,t.encoding.name,t.respond_to?(:tag)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-singleton-namespace-ignored"
begin
  o=Object.new;
  class<<o;
  CL299Case22=7;
  end;
  c=o.dup;
  p [o.singleton_class.const_defined?(:CL299Case22,false),c.singleton_class.const_defined?(:CL299Case22,false)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-hook-new-singleton"
begin
  class CL299Case23;
  def initialize_dup(o);
  def self.tag;
  7;
  end;
  super;
  end;
  end;
  c=CL299Case23.new.freeze.dup;
  p [c.tag,c.frozen?,c.singleton_class.frozen?]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-enumerator-singleton"
begin
  e=[1,2].each;
  def e.tag;
  7;
  end;
  c=e.dup;
  p [c.respond_to?(:tag),c.next,e.next]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-singleton-custom-dup-super"
begin
  o="x";
  def o.dup;
  super;
  end;
  c=o.dup;
  p [c,c.class,c.equal?(o)]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

nil
