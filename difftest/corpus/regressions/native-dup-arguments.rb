puts "dup-arity"
begin
  [Object.new,"x",[],{},StandardError.new("x")].each{|o|[[1],[1,2],[{}]].each{|a|begin;
  o.dup(*a);
  rescue=>e;
  p [e.class,e.message];
  end};
  begin;
  o.dup(freeze:false);
  rescue=>e;
  p [e.class,e.message];
  end;
  p o.dup(**{}).class}
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-immutable"
begin
  [nil,true,false,1,1.5,:x,Rational(1,2),Complex(1,2)].each{|o|p [o.class,o.dup.equal?(o),o.dup.frozen?];
  begin;
  o.dup(1);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  o.dup(freeze:false);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-direct-initialize"
begin
  o=Object.new;
  c=Object.new;
  p c.send(:initialize_dup,o).equal?(c);
  [[],[o,o]].each{|a|begin;
  c.send(:initialize_dup,*a);
  rescue=>e;
  p [e.class,e.message];
  end};
  begin;
  c.send(:initialize_dup,o,freeze:false);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-direct-hash-keyword"
begin
  h={};
  p h.send(:initialize_dup,foo:1);
  p h
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-direct-frozen"
begin
  o=Object.new.freeze;
  p o.send(:initialize_dup,o).equal?(o);
  begin;
  o.send(:initialize_dup,Object.new);
  rescue=>e;
  p [e.class,e.message];
  end;
  s="x".freeze;
  begin;
  s.send(:initialize_dup,s);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

nil
