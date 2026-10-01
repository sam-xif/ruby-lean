puts "constant-freeze-order"
begin
  m=Module.new.freeze;
  o=Object.new;
  def o.to_str;
  p :convert;
  "XL294Case20";
  end;
  ["bad",o,nil].each{|n|begin;
  m.const_set(n,1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-converter-freezes"
begin
  m=Module.new;
  o=Object.new;
  o.define_singleton_method(:to_str){m.freeze;
  "XL294Case21"};
  begin;
  m.const_set(o,1);
  rescue=>e;
  p [e.class,e.message,m.const_defined?(:XL294Case21,false)];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-converter-redefines-set"
begin
  module ML294Case23;
  end;
  o=Object.new;
  def o.to_str;
  def ML294Case23.const_set(*a);
  :replaced;
  end;
  "XL294Case23";
  end;
  p ML294Case23.const_set(o,1);
  p ML294Case23::XL294Case23;
  p ML294Case23.const_set(:YL294Case23,2)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-to-str-raise"
begin
  o=Object.new;
  def o.to_str;
  raise "stop";
  end;
  begin;
  Module.new.const_set(o,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-to-str-throw"
begin
  o=Object.new;
  def o.to_str;
  throw :stop,7;
  end;
  p catch(:stop){Module.new.const_set(o,1);
  :wrong}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-method-missing-raises"
begin
  class NL294Case32;
  def method_missing(n,*a);
  p n;
  raise NoMethodError,"no";
  end;
  def inspect;
  "NL294Case32";
  end;
  end;
  begin;
  Module.new.const_set(NL294Case32.new,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-promised-missing-raises"
begin
  class NL294Case33;
  def respond_to?(*a);
  p a;
  true;
  end;
  def method_missing(n,*a);
  p n;
  raise NoMethodError,"no";
  end;
  end;
  begin;
  Module.new.const_set(NL294Case33.new,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-return-from-converter"
begin
  def f;
  m=Module.new;
  o=Object.new;
  o.define_singleton_method(:to_str){return 7};
  m.const_set(o,1);
  9;
  end;
  p f
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-saved-target"
begin
  m=Module.new;
  n=Module.new;
  target=m;
  o=Object.new;
  o.define_singleton_method(:to_str){target=n;
  "XL294Case50"};
  p target.const_set(o,1);
  p [m.const_defined?(:XL294Case50,false),n.const_defined?(:XL294Case50,false)]
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

nil
