puts "constant-inspect-effect"
begin
  o=Object.new;
  def o.inspect;
  p :inspect;
  "CUSTOM";
  end;
  begin;
  Module.new.const_set(o,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-inspect-nonstr"
begin
  o=Object.new;
  def o.inspect;
  7;
  end;
  begin;
  Module.new.const_set(o,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-inspect-raise"
begin
  o=Object.new;
  def o.inspect;
  raise "inspect";
  end;
  begin;
  Module.new.const_set(o,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-inspect-fallback"
begin
  x=Object.new;
  y=Object.new;
  x.define_singleton_method(:inspect){p :inspect;
  y};
  def y.to_s;
  p :to_s;
  7;
  end;
  begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-inspect-to-s"
begin
  x=Object.new;
  y=Object.new;
  x.define_singleton_method(:inspect){y};
  def y.to_s;
  p :to_s;
  "NAME";
  end;
  begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-to-s-raise"
begin
  x=Object.new;
  y=Object.new;
  x.define_singleton_method(:inspect){y};
  def y.to_s;
  raise "render";
  end;
  begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-inspect-missing"
begin
  x=Object.new;
  class<<x;
  undef inspect;
  end;
  begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-inspect-private"
begin
  class NL294Case31;
  private;
  def inspect;
  p :inspect;
  "NL294Case31";
  end;
  end;
  begin;
  Module.new.const_set(NL294Case31.new,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-inspect-controls"
begin
  ["é","é\0","AL294Case51\nB","\0","a\\b",'a"b',"\u2028","\u{1D455}"].each{|s|x=Object.new;
  x.define_singleton_method(:inspect){s};
  begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end};
  nil
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-error-to-s-null"
begin
  x=Object.new;
  y=Object.new;
  x.define_singleton_method(:inspect){y};
  def y.to_s;
  "a\0b";
  end;
  begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

nil
