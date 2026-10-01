puts "copy-types"
begin
  [["old","new"], [[1],[2]], [{a:1},{b:2}]].each{|d,s|d.instance_variable_set(:@x,1);
  s.instance_variable_set(:@x,2);
  r=d.send(:initialize_copy,s);
  p [r.equal?(d),d,d.instance_variable_get(:@x)]}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-conversion"
begin
  s="old";
  o=Object.new;
  def o.to_str;
  p :convert;
  "new";
  end;
  p s.send(:initialize_copy,o);
  a=[];
  v=Object.new;
  def v.to_ary;
  p :array;
  [1,2];
  end;
  p a.send(:initialize_copy,v);
  h={};
  v=Object.new;
  def v.to_hash;
  p :hash;
  {a:1};
  end;
  p h.send(:initialize_copy,v)
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-conversion-errors"
begin
  ["a",[],{}].each{|d|[nil,1,Object.new].each{|s|begin;
  d.send(:initialize_copy,s);
  rescue=>e;
  p [e.class,e.message];
  end}}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-conversion-invalid"
begin
  [[:to_str,"a"],[:to_ary,[]],[:to_hash,{}]].each{|n,d|[nil,7,false].each{|r|o=Object.new;
  o.define_singleton_method(n){r};
  begin;
  d.send(:initialize_copy,o);
  rescue=>e;
  p [e.class,e.message];
  end}}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-freeze-before-conversion"
begin
  ["a",[],{}].each{|d|d.freeze;
  o=Object.new;
  def o.to_str;
  raise "wrong";
  end;
  def o.to_ary;
  raise "wrong";
  end;
  def o.to_hash;
  raise "wrong";
  end;
  begin;
  d.send(:initialize_copy,o);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-conversion-freezes-target"
begin
  s="a";
  v=Object.new;
  v.define_singleton_method(:to_str){s.freeze;
  "b"};
  begin;
  s.send(:initialize_copy,v);
  rescue=>e;
  p [e.class,e.message];
  end;
  p [s,s.frozen?];
  a=[1];
  v=Object.new;
  v.define_singleton_method(:to_ary){a.freeze;
  [2]};
  begin;
  a.send(:initialize_copy,v);
  rescue=>e;
  p [e.class,e.message];
  end;
  p [a,a.frozen?];
  h={a:1};
  v=Object.new;
  v.define_singleton_method(:to_hash){h.freeze;
  {b:2}};
  begin;
  h.send(:initialize_copy,v);
  rescue=>e;
  p [e.class,e.message];
  end;
  p [h,h.frozen?]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-hash-iteration"
begin
  h={a:1};
  h.each{|k,v|p h.send(:initialize_copy,h);
  begin;
  h.send(:initialize_copy,{});
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-arity"
begin
  ["a",[],{}].each{|d|[[],[1,2]].each{|a|begin;
  d.send(:initialize_copy,*a);
  rescue=>e;
  p [e.class,e.message];
  end}}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "copy-string-encoding"
begin
  s="x";
  t=255.chr;
  s.send(:initialize_copy,t);
  p [s.bytes,s.encoding.name,s.equal?(t)];
  s.send(:initialize_copy,"é");
  p [s,s.encoding.name]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

nil
