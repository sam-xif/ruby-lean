puts "binary-copy-subclass"
begin
  class SL296Case9<String;
  end;
  s=SL296Case9.new("abc");
  s.force_encoding("BINARY");
  t=s.b;
  p [s.class,t.class,t.equal?(s),t.frozen?,t.encoding.name]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-frozen-subclass"
begin
  class SL296Case10<String;
  end;
  s=SL296Case10.new("abc");
  s.force_encoding("BINARY");
  s.freeze;
  t=s.b;
  p [s.class,t.class,t.equal?(s),s.frozen?,t.frozen?];
  t << "x";
  p [s,t]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-native-alias"
begin
  class SL296Case11<String;
  alias bytes_copy b;
  def b;
  :override;
  end;
  end;
  s=SL296Case11.new("abc");
  s.force_encoding("BINARY");
  t=s.bytes_copy;
  p [s.b,t.class,t.equal?(s),t.frozen?]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-super"
begin
  class SL296Case12<String;
  def b;
  super;
  end;
  end;
  s=SL296Case12.new("abc");
  s.force_encoding("BINARY");
  t=s.b;
  p [t.class,t.equal?(s),t.frozen?,t.bytes]
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

puts "binary-copy-private-alias"
begin
  class SL296Case19<String;
  alias copy b;
  private :b;
  end;
  s=SL296Case19.new("abc");
  s.force_encoding("BINARY");
  p [s.copy.class,s.copy.equal?(s)];
  begin;
  s.b;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l296_error
  p [:caught, __l296_error.class, __l296_error.message]
end

nil
