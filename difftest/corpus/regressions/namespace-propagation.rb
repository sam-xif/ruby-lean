puts "name-known-nested"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case1,c);
  p [m.name,c.name];
  ML295Case1=m;
  p [m.name,c.name];
  NL295Case1=m;
  p [m.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-deep"
begin
  m=Module.new;
  c=Class.new;
  d=Module.new;
  c.const_set(:DL295Case2,d);
  m.const_set(:CL295Case2,c);
  p [m.name,c.name,d.name];
  ML295Case2=m;
  p [m.name,c.name,d.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-direct-promote"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case3,c);
  p c.name;
  CL295Case3=c;
  p c.name;
  ML295Case3=m;
  p [c.name,ML295Case3::CL295Case3.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-temporary-aliases"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  a.const_set(:CL295Case4,c);
  b.const_set(:DL295Case4,c);
  p c.name;
  BL295Case4=b;
  p c.name;
  AL295Case4=a;
  p c.name
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-permanent-alias"
begin
  module NamedL295Case5;
  end;
  m=Module.new;
  m.const_set(:Other,NamedL295Case5);
  ML295Case5=m;
  p [NamedL295Case5.name,ML295Case5::Other.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-inherited-not-owned"
begin
  a=Class.new;
  c=Class.new;
  a.const_set(:CL295Case12,c);
  b=Class.new(a);
  BL295Case12=b;
  p [a.name,c.name,BL295Case12::CL295Case12.name];
  AL295Case12=a;
  p c.name
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-private-child"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case13,c);
  m.private_constant(:CL295Case13);
  ML295Case13=m;
  p [c.name,ML295Case13.const_get(:CL295Case13).name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-native-prefix-bypasses-overrides"
begin
  m=Module.new;
  def m.name;
  "custom-name";
  end;
  def m.to_s;
  "custom-string";
  end;
  def m.inspect;
  "custom-inspect";
  end;
  c=Class.new;
  m.const_set(:CL295Case16,c);
  p c.name;
  ML295Case16=m;
  p c.name
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-three-stages"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  a.const_set(:BL295Case23,b);
  b.const_set(:CL295Case23,c);
  p [a.name,b.name,c.name];
  d=Module.new;
  d.const_set(:AL295Case23,a);
  p [a.name,b.name,c.name];
  DL295Case23=d;
  p [a.name,b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-child-first-permanent"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  b.const_set(:CL295Case24,c);
  a.const_set(:BL295Case24,b);
  BL295Case24=b;
  p [b.name,c.name];
  AL295Case24=a;
  p [a.name,b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-parent-first-permanent"
begin
  m=Module.new;
  ML295Case25=m;
  c=Class.new;
  d=Class.new;
  c.const_set(:DL295Case25,d);
  m.const_set(:CL295Case25,c);
  p [c.name,d.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-detached-parent"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  b.const_set(:CL295Case31,c);
  a.const_set(:BL295Case31,b);
  a.const_set(:BL295Case31,nil);
  AL295Case31=a;
  p [a.name,b.name,c.name];
  BL295Case31=b;
  p [b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-only-own-constants"
begin
  a=Class.new;
  b=Module.new;
  c=Class.new;
  b.const_set(:CL295Case32,c);
  a.const_set(:BL295Case32,b);
  d=Class.new(a);
  DL295Case32=d;
  p [b.name,c.name];
  AL295Case32=a;
  p [b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-uninitialized-class"
begin
  m=Module.new;
  c=Class.allocate;
  d=Class.new;
  c.const_set(:DL295Case37,d);
  m.const_set(:CL295Case37,c);
  ML295Case37=m;
  p [c.name,d.name];
  c.send(:initialize);
  p [c.name,d.name,c.superclass]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-unicode-names"
begin
  m=Module.new;
  c=Class.new;
  d=Class.new;
  c.const_set("ǅ",d);
  m.const_set("É",c);
  ML295Case44=m;
  p [c.name,d.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

nil
