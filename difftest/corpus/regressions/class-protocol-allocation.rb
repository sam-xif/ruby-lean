puts "class-new-class"
begin
  begin;
  p Class.new(Class);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-new-nil"
begin
  begin;
  p Class.new(nil);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-allocate-state"
begin
  c=Class.allocate;
  p c.name;
  begin;
  p c.superclass;
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  p c.new;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-native-initialize"
begin
  c=Class.allocate;
  p c.send(:initialize,Array).equal?(c);
  p c.superclass;
  begin;
  c.send(:initialize);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "uninitialized-allocate"
begin
  c=Class.allocate;
  begin;
  c.allocate;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "uninitialized-super"
begin
  c=Class.allocate;
  begin;
  Class.new(c);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  class CL291Case18<c;
  end;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "forbidden-super"
begin
  [Class,Object.singleton_class,nil,true,false,1,Object.new].each{|s|begin;
  Class.new(s);
  rescue=>e;
  p [e.class,e.message];
  end}
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "named-nil"
begin
  begin;
  class CL291Case20<nil;
  end;
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  class DL291Case20<Class;
  end;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-initialize-order"
begin
  c=Class.allocate;
  c.freeze;
  begin;
  c.send(:initialize,Object,Object);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  String.send(:initialize,Object,Object);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-initialize-arity"
begin
  c=Class.allocate;
  begin;
  c.send(:initialize,Object,Object);
  rescue=>e;
  p [e.class,e.message];
  end;
  p c.send(:initialize).superclass
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-keywords"
begin
  begin;
  Class.new(x:1);
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  Module.new(x:1);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-initialize-frozen-native"
begin
  c=Class.allocate.freeze;
  p [c.send(:initialize).equal?(c),c.superclass,c.frozen?];
  begin;
  c.send(:initialize);
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-uninitialized-ancestry"
begin
  c=Class.allocate;
  p [c.ancestors==[c],c.singleton_class.superclass];
  UL291Case41=c;
  class DL291Case41<UL291Case41;
  end;
  begin;
  p DL291Case41.superclass;
  rescue=>e;
  p e.message;
  end;
  begin;
  DL291Case41.new;
  rescue=>e;
  p e.message;
  end;
  c.send(:initialize);
  begin;
  p DL291Case41.superclass;
  rescue=>e;
  p e.message;
  end;
  begin;
  DL291Case41.new;
  rescue=>e;
  p e.message;
  end;
  begin;
  DL291Case41.send(:initialize);
  rescue=>e;
  p e.message;
  end;
  p Class.new(DL291Case41).class
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-singleton-allocation"
begin
  c=Object.singleton_class;
  begin;
  c.new;
  rescue=>e;
  p [e.class,e.message];
  end;
  begin;
  c.allocate;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

puts "class-allocator-name-effect"
begin
  UL291Case53=Class.allocate;
  class DL291Case53<UL291Case53;
  def self.to_s;
  p :effect;
  "DERIVED";
  end;
  end;
  begin;
  DL291Case53.new;
  rescue=>e;
  p [e.class,e.message];
  end
rescue Exception => __l291_error
  p [:caught, __l291_error.class, __l291_error.message]
end

nil
