puts "name-frozen-mutation"
begin
  class CL297Case1;
  end;
  s=CL297Case1.name;
  p [s.frozen?,s.equal?(CL297Case1.name),s.class];
  begin;
  s << "bad";
  rescue=>e;
  p [e.class,e.message];
  end;
  p CL297Case1.name
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-dup"
begin
  class CL297Case9;
  end;
  s=CL297Case9.name;
  d=s.dup;
  p [s.frozen?,d.frozen?,s.equal?(d)];
  d << "copy";
  p [d,CL297Case9.name]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-hash-key"
begin
  class CL297Case20;
  end;
  s=CL297Case20.name;
  h={s=>1};
  p [h.keys.first.equal?(s),h.keys.first.equal?(CL297Case20.name),h[CL297Case20.name]]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-ivars-rejected"
begin
  class CL297Case24;
  end;
  s=CL297Case24.name;
  begin;
  s.instance_variable_set(:@x,1);
  rescue=>e;
  p [e.class,e.message];
  end;
  p CL297Case24.name
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-clone-default"
begin
  class CL297Case28;
  end;
  s=CL297Case28.name;
  t=s.clone;
  p [s.equal?(t),s.frozen?,t.frozen?,t.class]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

puts "name-binary-copy-permanent"
begin
  class CL297Case29;
  end;
  s=CL297Case29.name;
  t=s.b;
  p [s.frozen?,t.frozen?,s.equal?(t),t.equal?(CL297Case29.name),t.encoding.name];
  t << "copy";
  p [t,CL297Case29.name]
rescue Exception => __l297_error
  p [:caught, __l297_error.class, __l297_error.message]
end

nil
