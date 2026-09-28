puts "name-native-alias"
begin
  m=Module.new;
  class<<m;
  alias native_name name;
  def name;
  :override;
  end;
  end;
  p m.native_name;
  ML297Case2=m;
  p [m.name,m.native_name,m.native_name.frozen?,m.native_name.equal?(m.native_name)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-super"
begin
  class MCL297Case3<Module;
  def name;
  super;
  end;
  end;
  m=MCL297Case3.new;
  ML297Case3=m;
  p [m.name,m.name.equal?(m.name),m.name.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-core"
begin
  [Object,Module,Class,String,Enumerable,ArgumentError].each{|c|p [c.name,c.name.frozen?,c.name.equal?(c.name)]}
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-repr-fresh"
begin
  class CL297Case10;
  end;
  [:to_s,:inspect].each{|n|a=CL297Case10.send(n);
  b=CL297Case10.send(n);
  p [a,b,a.frozen?,a.equal?(b)];
  a << "copy";
  p CL297Case10.name}
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-singleton-cache"
begin
  o=Object.new;
  e=o.singleton_class;
  p e.name;
  EL297Case11=e;
  p [e.name,e.name.frozen?,e.name.equal?(e.name),e.to_s]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-frozen-namespace"
begin
  m=Module.new;
  m.freeze;
  ML297Case12=m;
  p [ML297Case12.name.frozen?,ML297Case12.name.equal?(ML297Case12.name),ML297Case12.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-arity"
begin
  class CL297Case13;
  end;
  [:name,:to_s,:inspect].each{|n|begin;
  p CL297Case13.send(n,1);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  p CL297Case13.send(n,x:1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-anonymous"
begin
  m=Module.new;
  p [m.name,m.name.equal?(m.name)];
  ML297Case14=m;
  p [m.name,m.name.equal?(m.name)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-alias-binding"
begin
  a=Class.new;
  AL297Case15=a;
  s=AL297Case15.name;
  BL297Case15=a;
  p [s.equal?(BL297Case15.name),BL297Case15.name,BL297Case15.name.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-unicode"
begin
  module ÉL297Case18;
  end;
  s=ÉL297Case18.name;
  p [s.frozen?,s.equal?(ÉL297Case18.name),s.encoding.name];
  m=Module.new;
  c=Class.new;
  m.const_set("ǅ",c);
  x=c.name;
  p [x.frozen?,x.equal?(c.name),x.encoding.name];
  ML297Case18=m;
  p [x,c.name,c.name.frozen?,c.name.encoding.name]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-cache-survives-writes"
begin
  class CL297Case21;
  end;
  s=CL297Case21.name;
  20.times{Object.new};
  class CL297Case21;
  attr_accessor :x;
  end;
  c=CL297Case21.new;
  c.x=7;
  a=[];
  a<<1;
  h={};
  h[:a]=2;
  p [s.equal?(CL297Case21.name),CL297Case21.name.frozen?,c.x,a,h]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-feature-load"
begin
  s=String.name;
  require "uri";
  p [s.equal?(String.name),URI.name.frozen?,URI.name.equal?(URI.name)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

nil
