puts "binary-copy-identity"
begin
  s=255.chr;
  a=s.b;
  b=s.b;
  p [a.equal?(s),a.equal?(b),a.frozen?,a.encoding.name,a.bytes]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-mutation"
begin
  s=255.chr;
  t=s.b;
  t << "x";
  p [s.bytes,t.bytes,s.equal?(t)]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-frozen"
begin
  s=255.chr.freeze;
  t=s.b;
  p [t.equal?(s),s.frozen?,t.frozen?];
  t << "x";
  p [s.bytes,t.bytes]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-empty"
begin
  s="".force_encoding("BINARY").freeze;
  a=s.b;
  b=s.b;
  p [a.equal?(s),a.equal?(b),a.frozen?,a.bytes];
  a << "x";
  p [s.bytes,a.bytes]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-ivars"
begin
  s=255.chr;
  s.instance_variable_set(:@x,7);
  t=s.b;
  p [s.instance_variables,t.instance_variables,t.class,t.frozen?]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-eigenclass"
begin
  s=255.chr;
  def s.tag;
  :tag;
  end;
  t=s.b;
  p [s.tag,t.respond_to?(:tag),t.class]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-conversion-bypass"
begin
  s=255.chr;
  def s.to_s;
  raise "wrong";
  end;
  def s.to_str;
  raise "wrong";
  end;
  t=s.b;
  p [t.bytes,t.equal?(s)]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-block-and-arity"
begin
  s=255.chr;
  t=s.b{raise "wrong"};
  p t.equal?(s);
  [ [1], [{x:1}] ].each{|a|begin;
  s.b(*a);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-forced-receiver"
begin
  s="é";
  s.force_encoding("BINARY");
  t=s.b;
  p [s.bytes,t.bytes,t.equal?(s)];
  s << "x";
  p [s.bytes,t.bytes]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-helper-override"
begin
  s=255.chr;
  def s.__as_binary;
  :wrong;
  end;
  p s.b
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-helper-absent"
begin
  p "abc".respond_to?(:__as_binary,true)
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-ascii-append"
begin
  s="abc".force_encoding("BINARY");
  t=s.b;
  t << "x";
  p [s,t,t.equal?(s),t.encoding.name]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

nil
