puts "dup-object-fields"
begin
  class CL299Case2;
  attr_accessor :x;
  end;
  o=CL299Case2.new;
  o.x=[];
  c=o.dup;
  p [c.class,c.equal?(o),c.x.equal?(o.x)];
  c.x=7;
  p [o.x,c.x]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-binary"
begin
  o=255.chr.freeze;
  c=o.dup;
  c << "x";
  p [o.bytes,c.bytes,c.frozen?,c.equal?(o),c.encoding.name]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-mutates-source"
begin
  class SL299Case10<String;
  def initialize_dup(o);
  o << "changed";
  super;
  end;
  end;
  s=SL299Case10.new("x");
  p [s.dup,s]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-allocation-bypass"
begin
  class CL299Case34;
  end;
  o=CL299Case34.new;
  class CL299Case34;
  def self.new;
  raise "wrong";
  end;
  def self.allocate;
  raise "wrong";
  end;
  def initialize;
  raise "wrong";
  end;
  end;
  p o.dup.class
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-shared-default"
begin
  h=Hash.new([]);
  h[:a]=[1];
  c=h.dup;
  p [c[:z].equal?(h[:z]),c[:a].equal?(h[:a])];
  c[:b]=2;
  p [h,c]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-default-proc"
begin
  h=Hash.new{|s,k|p s.class;
  k.to_s};
  p h.dup[:a]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-enumerator"
begin
  e=[1,2].each;
  c=e.dup;
  p [e.next,c.next,e.next,c.next];
  begin;
  e.dup;
  rescue=>x;
  p [x.class,x.message];
  end
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-regexp-range"
begin
  [Regexp.new("x").freeze,1..2].each{|o|c=o.dup;
  p [c,c.equal?(o),c.frozen?]}
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-string-frozen-name"
begin
  class CL299Case40;
  end;
  s=CL299Case40.name;
  c=s.dup;
  p [s.frozen?,c.frozen?,c.equal?(s)];
  c << "copy";
  p [c,CL299Case40.name]
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

puts "dup-source-ivars"
begin
  class CL299Case41;
  def initialize_dup(o);
  o.instance_variable_set(:@x,2);
  p [@x,o.instance_variable_get(:@x)];
  super;
  p @x;
  end;
  end;
  o=CL299Case41.new;
  o.instance_variable_set(:@x,1);
  o.dup;
  nil
rescue Exception => __l299_error
  p [:caught, __l299_error.class, __l299_error.message]
end

nil
