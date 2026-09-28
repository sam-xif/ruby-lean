puts "name-freeze-child"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case6,c);
  c.freeze;
  ML295Case6=m;
  p [c.name,c.frozen?]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-freeze-parent"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case7,c);
  m.freeze;
  ML295Case7=m;
  p [m.name,c.name,m.frozen?]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-no-descendant-hooks"
begin
  m=Module.new;
  c=Class.new;
  d=Class.new;
  def m.const_added(n);
  p [:m,n];
  end;
  def c.const_added(n);
  p [:c,n];
  end;
  c.const_set(:DL295Case15,d);
  m.const_set(:CL295Case15,c);
  ML295Case15=m;
  p [c.name,d.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-frozen-whole-tree"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  b.const_set(:CL295Case26,c);
  a.const_set(:BL295Case26,b);
  a.freeze;
  b.freeze;
  c.freeze;
  AL295Case26=a;
  p [a.name,b.name,c.name,a.frozen?,b.frozen?,c.frozen?]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-promotion-bypasses-descendant-hooks"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  b.const_set(:CL295Case30,c);
  a.const_set(:BL295Case30,b);
  def a.const_added(n);
  raise "wrong";
  end;
  def b.const_added(n);
  raise "wrong";
  end;
  AL295Case30=a;
  p [a.name,b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-frozen-host-no-promotion"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case45,c);
  host=Module.new.freeze;
  begin;
  host.const_set(:ML295Case45,m);
  rescue=>e;
  p [e.class,m.name,c.name];
  end
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-method-error-after-promotion"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case46,c);
  ML295Case46=m;
  begin;
  c.send(:remove_method,:missing);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-temporary-method-error"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case47,c);
  begin;
  c.send(:remove_method,:missing);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

nil
