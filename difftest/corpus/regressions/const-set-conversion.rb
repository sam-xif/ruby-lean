puts "constant-to-str"
begin
  module ML294Case10;
  def self.const_added(n);
  p n;
  end;
  end;
  o=Object.new;
  def o.to_str;
  p :convert;
  "XL294Case10";
  end;
  p ML294Case10.const_set(o,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-private-converter"
begin
  class NL294Case11;
  private;
  def to_str;
  p :convert;
  "XL294Case11";
  end;
  end;
  m=Module.new;
  p m.const_set(NL294Case11.new,3);
  p m.const_get(:XL294Case11)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-response-false"
begin
  class NL294Case12;
  def respond_to?(*a);
  p a;
  false;
  end;
  def to_str;
  p :wrong;
  "XL294Case12";
  end;
  def inspect;
  "NL294Case12";
  end;
  end;
  begin;
  Module.new.const_set(NL294Case12.new,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-method-missing"
begin
  class NL294Case13;
  def method_missing(n,*a);
  p [n,a];
  return "XL294Case13" if n==:to_str;
  super;
  end;
  end;
  p Module.new.const_set(NL294Case13.new,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-response-missing"
begin
  class NL294Case14;
  def respond_to_missing?(n,p);
  p [n,p];
  n==:to_str;
  end;
  def method_missing(n,*a);
  p n;
  "XL294Case14";
  end;
  end;
  p Module.new.const_set(NL294Case14.new,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-bad-conversion"
begin
  [nil,false,1,:XL294Case15,[]].each{|x|o=Object.new;
  o.define_singleton_method(:to_str){x};
  begin;
  Module.new.const_set(o,1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-missing-conversion"
begin
  [nil,true,false,1,1.5,Object.new].each{|x|begin;
  Module.new.const_set(x,1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-response-installs"
begin
  class NL294Case34;
  def respond_to?(n,*a);
  p n;
  def to_str;
  p :convert;
  "XL294Case34";
  end;
  true;
  end;
  end;
  m=Module.new;
  p m.const_set(NL294Case34.new,1);
  p m.const_get(:XL294Case34)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-response-one-arg"
begin
  class NL294Case35;
  def respond_to?(n);
  p n;
  true;
  end;
  def to_str;
  "XL294Case35";
  end;
  end;
  p Module.new.const_set(NL294Case35.new,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-response-missing-false"
begin
  class NL294Case36;
  def respond_to_missing?(n,p);
  puts n;
  false;
  end;
  def method_missing(n,*a);
  p :wrong;
  "XL294Case36";
  end;
  def inspect;
  "NL294Case36";
  end;
  end;
  begin;
  Module.new.const_set(NL294Case36.new,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-converter-arity"
begin
  class NL294Case37;
  def to_str(a);
  a;
  end;
  end;
  begin;
  Module.new.const_set(NL294Case37.new,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-conversion-then-hook"
begin
  module ML294Case39;
  def self.const_added(n);
  p [n,const_get(n,false)];
  end;
  end;
  o=Object.new;
  def o.to_str;
  p :convert;
  "XL294Case39";
  end;
  p ML294Case39.const_set(o,7)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-conversion-invalid"
begin
  o=Object.new;
  def o.to_str;
  p :convert;
  "bad";
  end;
  begin;
  Module.new.const_set(o,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-conversion-result-subclass"
begin
  class SL294Case41<String;
  def to_s;
  raise "wrong";
  end;
  def to_str;
  raise "wrong";
  end;
  end;
  o=Object.new;
  o.define_singleton_method(:to_str){SL294Case41.new("XL294Case41")};
  m=Module.new;
  p m.const_set(o,1);
  p m.const_get(:XL294Case41)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-string-no-conversion"
begin
  s="XL294Case42";
  def s.to_str;
  raise "wrong";
  end;
  def s.inspect;
  raise "wrong";
  end;
  def s.to_s;
  raise "wrong";
  end;
  p Module.new.const_set(s,1)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

nil
