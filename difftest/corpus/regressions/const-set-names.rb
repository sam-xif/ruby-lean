puts "constant-invalid-string-name"
begin
  module ML294Case1;
  def self.const_added(n);
  p [:wrong,n];
  end;
  end;
  ["x","AL294Case1::BL294Case1","","::AL294Case1","AL294Case1 BL294Case1","AL294Case1!","_A","1A","AL294Case1=","AL294Case1?","AL294Case1
"].each{|n|begin;
  ML294Case1.const_set(n,1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-invalid-symbol-name"
begin
  module ML294Case2;
  end;
  [:x,:"AL294Case2::BL294Case2",:"",:"@AL294Case2",:"AL294Case2!",:"$AL294Case2"].each{|n|begin;
  ML294Case2.const_set(n,1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-unicode-names"
begin
  module ML294Case3;
  end;
  ["À","ǅ","Ⅰ","Ⓐ","𝐀","İ","K","µ","é","AL294Case3😀","AL294Case3 ","Aé","AL294Case3 "].each{|n|begin;
  p ML294Case3.const_set(n,1);
  p ML294Case3.const_get(n);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-name-subclass"
begin
  class SL294Case22<String;
  def to_str;
  raise "wrong";
  end;
  def to_s;
  raise "wrong";
  end;
  end;
  m=Module.new;
  p m.const_set(SL294Case22.new("XL294Case22"),1);
  begin;
  m.const_set(SL294Case22.new("bad"),1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-name-controls"
begin
  m=Module.new;
  ["AL294Case26\0B","AL294Case26\nB","AL294Case26\tB","AL294Case26\eB","AL294Case26\rB","AL294Case26\u0001B","AL294Case26\"BL294Case26","AL294Case26\\BL294Case26"].each{|n|begin;
  m.const_set(n,1);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-valid-value-identity"
begin
  m=Module.new;
  x=[];
  p m.const_set("XL294Case38",x).equal?(x);
  p m.const_get(:XL294Case38).equal?(x);
  p m.const_set(:XL294Case38,nil);
  p m.const_get(:XL294Case38)
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

puts "constant-name-bytes-ascii"
begin
  m=Module.new;
  p m.const_set("XL294Case44".b,1);
  begin;
  m.const_set("bad".b,1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l294_error
  p [:caught, __l294_error.class, __l294_error.message]
end

nil
