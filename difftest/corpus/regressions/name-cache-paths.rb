puts "name-temp-promotion"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL297Case4,c);
  s=c.name;
  p [s.frozen?,s.equal?(c.name)];
  ML297Case4=m;
  p [s,c.name,s.equal?(c.name),c.name.equal?(c.name),c.name.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-same-top-path"
begin
  a=Class.new;
  Object.const_set(:AL297Case6,a);
  x=a.name;
  b=Class.new;
  Object.const_set(:AL297Case6,b);
  p [x.equal?(b.name),x.frozen?,b.name.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-same-nested-path"
begin
  module ML297Case7;
  end;
  a=Class.new;
  ML297Case7.const_set(:AL297Case7,a);
  x=a.name;
  b=Class.new;
  ML297Case7.const_set(:AL297Case7,b);
  p [x.equal?(b.name),x.frozen?,b.name.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-replaced-temp-path"
begin
  m=Module.new;
  a=Class.new;
  m.const_set(:AL297Case8,a);
  x=a.name;
  b=Class.new;
  m.const_set(:AL297Case8,b);
  p [x.equal?(b.name),x.frozen?,b.name.frozen?];
  ML297Case8=m;
  p [x,a.name,b.name,x.equal?(a.name)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-temp-alias-binding"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  a.const_set(:CL297Case16,c);
  s=c.name;
  b.const_set(:D,c);
  p [s.equal?(c.name),c.name];
  CL297Case16=c;
  p [c.name,s.equal?(c.name),s.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-deep-snapshots"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  a.const_set(:BL297Case17,b);
  b.const_set(:CL297Case17,c);
  s=b.name;
  t=c.name;
  AL297Case17=a;
  p [s,t,b.name,c.name,s.equal?(b.name),t.equal?(c.name),b.name.equal?(b.name),c.name.equal?(c.name)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-binary-temp"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL297Case19,c);
  s=c.name;
  p [s.frozen?,s.encoding.name,s.equal?(c.name)];
  d=s.dup;
  p [d.frozen?,d.encoding.name]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-binary-copy-temporary"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL297Case30,c);
  s=c.name;
  t=s.b;
  p [s.frozen?,t.frozen?,s.equal?(t),t.encoding.name];
  t << "copy";
  p [s,c.name,t,c.name.equal?(s)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-readonly-promotion"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL297Case31,c);
  s=c.name;
  begin;
  s << "bad";
  rescue=>e;
  p e.class;
  end;
  ML297Case31=m;
  p [s,c.name,s.frozen?,c.name.frozen?]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-joined-promotions"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL297Case32,c);
  ML297Case32=m;
  s=c.name;
  n=Module.new;
  d=Class.new;
  n.const_set(:CL297Case32,d);
  Object.const_set(:ML297Case32,n);
  p [s,c.name,d.name,s.equal?(d.name),d.name.equal?(d.name)]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

nil
