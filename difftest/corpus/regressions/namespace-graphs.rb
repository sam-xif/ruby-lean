puts "name-self-cycle"
begin
  m=Module.new;
  m.const_set(:SelfL295Case8,m);
  p m.name;
  ML295Case8=m;
  p [m.name,ML295Case8::SelfL295Case8.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-mutual-cycle"
begin
  a=Module.new;
  b=Module.new;
  a.const_set(:BL295Case9,b);
  b.const_set(:AL295Case9,a);
  p [a.name,b.name];
  AL295Case9=a;
  p [a.name,b.name,b.const_get(:AL295Case9).name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-replace-edge"
begin
  m=Module.new;
  c=Class.new;
  d=Class.new;
  m.const_set(:AL295Case10,c);
  m.const_set(:BL295Case10,c);
  m.const_set(:AL295Case10,d);
  ML295Case10=m;
  p [c.name,d.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-only-live-edge"
begin
  m=Module.new;
  c=Class.new;
  m.const_set(:CL295Case11,c);
  m.const_set(:CL295Case11,1);
  ML295Case11=m;
  p [m.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-sibling-cycles"
begin
  a=Module.new;
  b=Module.new;
  c=Module.new;
  a.const_set(:BL295Case33,b);
  a.const_set(:CL295Case33,c);
  b.const_set(:RootL295Case33,a);
  c.const_set(:RootL295Case33,a);
  AL295Case33=a;
  p [a.name,b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-three-cycle"
begin
  a=Module.new;
  b=Module.new;
  c=Module.new;
  a.const_set(:BL295Case34,b);
  b.const_set(:CL295Case34,c);
  c.const_set(:AL295Case34,a);
  AL295Case34=a;
  p [a.name,b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-late-back-edge"
begin
  a=Module.new;
  b=Module.new;
  a.const_set(:BL295Case35,b);
  AL295Case35=a;
  b.const_set(:RootL295Case35,a);
  p [a.name,b.name,b.const_get(:RootL295Case35).name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-permanent-cross-edges"
begin
  a=Module.new;
  b=Module.new;
  c=Class.new;
  CL295Case36=c;
  a.const_set(:CL295Case36,c);
  b.const_set(:CL295Case36,c);
  m=Module.new;
  m.const_set(:AL295Case36,a);
  m.const_set(:BL295Case36,b);
  ML295Case36=m;
  p [a.name,b.name,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

nil
