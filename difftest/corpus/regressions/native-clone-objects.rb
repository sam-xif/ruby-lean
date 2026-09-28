puts "clone-freeze-matrix"
begin
  [Object.new,"abc",[1],{a:1}].each{|o|[false,true].each{|f|o.freeze if f;
  [nil,true,false].each{|mode|c=o.clone(freeze:mode);
  p [o.class,o.frozen?,mode,c.frozen?,c.equal?(o)]}}}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-super-native"
begin
  class SL298Case25<String;
  def clone(**kw);
  super;
  end;
  end;
  o=SL298Case25.new("abc").freeze;
  p [o.clone(freeze:false),o.clone(freeze:false).frozen?]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-native-alias"
begin
  class SL298Case26<String;
  alias native_clone clone;
  def clone;
  :wrong;
  end;
  end;
  o=SL298Case26.new("abc").freeze;
  p [o.clone,o.native_clone(freeze:false),o.native_clone(freeze:false).frozen?]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-direct-initialize-clone"
begin
  a=Object.new;
  b=Object.new;
  [nil,false,true,0].each{|f|begin;
  p a.send(:initialize_clone,b,freeze:f).equal?(a);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-direct-copy-frozen"
begin
  s="a".freeze;
  p s.send(:initialize_copy,s);
  begin;
  s.send(:initialize_clone,"b",freeze:false);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-initialize-clone-alias"
begin
  class CL298Case29;
  alias native_init initialize_clone;
  def initialize_clone(o,**kw);
  native_init(o,**kw);
  @ok=1;
  end;
  attr_reader :ok;
  end;
  o=CL298Case29.new.freeze;
  p [o.clone(freeze:false).ok,o.clone(freeze:false).frozen?]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-exception"
begin
  e=ArgumentError.new("x").freeze;
  c=e.clone(freeze:false);
  p [c.class,c.message,c.frozen?,e.equal?(c),e.message.equal?(c.message)]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-new-allocate-bypass"
begin
  class CL298Case38;
  end;
  o=CL298Case38.new;
  class CL298Case38;
  def self.new;
  raise "wrong";
  end;
  def self.allocate;
  raise "wrong";
  end;
  def initialize;
  raise "wrong";
  end;
  end;
  p o.clone.class
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-source-freeze-override"
begin
  class CL298Case56;
  def frozen?;
  false;
  end;
  def freeze;
  raise "wrong";
  end;
  end;
  o=CL298Case56.new;
  o.send(:initialize_copy,o);
  p o.clone(freeze:true).instance_variable_get(:@x);
  nil
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

nil
