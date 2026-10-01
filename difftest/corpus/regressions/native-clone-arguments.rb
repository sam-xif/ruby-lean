puts "clone-object-keyword"
begin
  o=Object.new.freeze;
  a=o.clone(freeze:false);
  b=o.clone(freeze:true);
  p [a.frozen?,b.frozen?,a.equal?(o),b.equal?(o)]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-array-keyword"
begin
  o=[1].freeze;
  a=o.clone(freeze:false);
  b=o.clone(freeze:true);
  p [a.frozen?,b.frozen?,a.equal?(o),b.equal?(o)]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hash-keyword"
begin
  o={a:1}.freeze;
  a=o.clone(freeze:false);
  b=o.clone(freeze:true);
  p [a.frozen?,b.frozen?,a.equal?(o),b.equal?(o)]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-string-keyword"
begin
  o="abc".freeze;
  a=o.clone(freeze:false);
  b=o.clone(freeze:true);
  p [a.frozen?,b.frozen?,a.equal?(o),b.equal?(o)]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-binary-keyword"
begin
  o=255.chr.freeze;
  a=o.clone(freeze:false);
  b=o.clone(freeze:true);
  p [a.frozen?,b.frozen?,a.bytes,b.bytes,a.encoding.name,b.encoding.name]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-frozen-values"
begin
  [nil,true,false,1,1.5,:sym].each{|v|begin;
  r=v.clone(freeze:false);
  p [r,v.equal?(r),r.frozen?];
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-keyword-validation"
begin
  [nil,0,:x,true,false].each{|v|begin;
  r="a".clone(freeze:v);
  p [v,r.frozen?];
  rescue=>e;
  p [e.class,e.message];
  end};
  begin;
  "a".clone(other:1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-positional-hash"
begin
  begin;
  "a".clone({freeze:false});
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-numeric-immutable"
begin
  [Rational(1,2),Complex(1,2)].each{|o|[nil,true,false].each{|f|begin;
  c=o.clone(freeze:f);
  p [c.equal?(o),c.frozen?];
  rescue=>e;
  p [e.class,e.message];
  end}}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-empty-keywords"
begin
  p ["a".clone(**{}),"a".clone{raise "wrong"}]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-arg-priority"
begin
  begin;
  "a".clone(1,other:2,freeze:0);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  "a".clone(other:2,freeze:0);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-key-nonsymbol"
begin
  begin;
  "a".clone(**{"freeze"=>false,3=>1});
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-key-symbols"
begin
  begin;
  "a".clone(foo:1,bar:2);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-unknown-key-inspect"
begin
  k=Object.new;
  def k.inspect;
  p :inspected;
  "KEY";
  end;
  begin;
  Object.new.clone(**{k=>1});
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-invalid-freeze-class"
begin
  class FL298Case34;
  def self.to_s;
  p :class_name;
  "SPECIAL";
  end;
  end;
  begin;
  Object.new.clone(freeze:FL298Case34.new);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-key-inspect-nonstr"
begin
  k=Object.new;
  def k.inspect;
  7;
  end;
  begin;
  Object.new.clone(**{k=>1});
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-key-inspect-raises"
begin
  k=Object.new;
  def k.inspect;
  raise "inspect";
  end;
  begin;
  Object.new.clone(**{k=>1});
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-freeze-class-bad-tos"
begin
  class CL298Case54;
  def self.to_s;
  7;
  end;
  end;
  begin;
  Object.new.clone(freeze:CL298Case54.new);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

nil
