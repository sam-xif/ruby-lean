puts "binary-copy-utf8"
begin
  s="é😀";
  t=s.b;
  p [s.length,t.length,t.bytes,t.frozen?,t.equal?(s)];
  t << "x";
  p [s,t.bytes]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-ascii-utf8"
begin
  s="abc".freeze;
  t=s.b;
  t << "x";
  p [s,t,t.frozen?,t.equal?(s),t.encoding.name]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

nil
