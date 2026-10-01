puts "name-module-subclass"
begin
  class MML295Case17<Module;
  end;
  m=MML295Case17.new;
  c=Class.new;
  m.const_set(:CL295Case17,c);
  p c.name;
  ML295Case17=m;
  p c.name
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-singleton-container"
begin
  m=Module.new;
  e=m.singleton_class;
  c=Class.new;
  e.const_set(:CL295Case18,c);
  p c.name;
  ML295Case18=m;
  p [e.name,c.name];
  EL295Case18=e;
  p [e.name,c.name,e.to_s]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-singleton-value"
begin
  o=Object.new;
  e=o.singleton_class;
  m=Module.new;
  m.const_set(:EL295Case19,e);
  p [e.name,e.to_s];
  ML295Case19=m;
  p [e.name,e.to_s]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-scoped-object"
begin
  class Object::CL295Case20;
  end;
  module Object::ML295Case20;
  end;
  p [CL295Case20.name,ML295Case20.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-scoped-anonymous"
begin
  m=Module.new;
  class m::CL295Case21;
  end;
  module m::NL295Case21;
  end;
  c=m.const_get(:CL295Case21);
  n=m.const_get(:NL295Case21);
  p [c.name,n.name];
  ML295Case21=m;
  p [c.name,n.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-lexical-anonymous"
begin
  m=Module.new;
  m.module_eval{class CL295Case22;
  end;
  module NL295Case22;
  end};
  p [m.const_get(:CL295Case22).name,m.const_get(:NL295Case22).name];
  ML295Case22=m;
  p [ML295Case22::CL295Case22.name,ML295Case22::NL295Case22.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-qualified-global"
begin
  module Object::ML295Case38;
  class CL295Case38;
  end;
  end;
  p [ML295Case38.name,ML295Case38::CL295Case38.name];
  class Object::NL295Case38;
  class DL295Case38;
  end;
  end;
  p [NL295Case38.name,NL295Case38::DL295Case38.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-anonymous-scoped-body"
begin
  m=Module.new;
  class m::CL295Case39;
  class DL295Case39;
  end;
  end;
  c=m.const_get(:CL295Case39);
  p [c.name,c::DL295Case39.name];
  ML295Case39=m;
  p [c.name,c::DL295Case39.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-scoped-eigenclass"
begin
  o=Object.new;
  e=o.singleton_class;
  class e::CL295Case40;
  end;
  module e::ML295Case40;
  end;
  p [e::CL295Case40.name,e::ML295Case40.name];
  EL295Case40=e;
  p [e::CL295Case40.name,e::ML295Case40.name,e.to_s]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-lexical-eigenclass"
begin
  o=Object.new;
  class<<o;
  class CL295Case41;
  end;
  module ML295Case41;
  end;
  end;
  e=o.singleton_class;
  p [e::CL295Case41.name,e::ML295Case41.name];
  EL295Case41=e;
  p [e::CL295Case41.name,e::ML295Case41.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-named-eigenclass-prefix"
begin
  o=Object.new;
  e=o.singleton_class;
  EL295Case42=e;
  c=Class.new;
  e.const_set(:CL295Case42,c);
  p [e.name,e.to_s,c.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

puts "name-module-subclass-eigenclass-prefix"
begin
  class MCL295Case43<Module;
  end;
  m=MCL295Case43.new;
  e=m.singleton_class;
  c=Class.new;
  m.const_set(:CL295Case43,c);
  p c.name;
  EL295Case43=e;
  d=Class.new;
  m.const_set(:DL295Case43,d);
  p [c.name,d.name];
  ML295Case43=m;
  p [c.name,d.name]
rescue Exception => __l295_error
  p [:caught, __l295_error.class, __l295_error.message]
end

nil
