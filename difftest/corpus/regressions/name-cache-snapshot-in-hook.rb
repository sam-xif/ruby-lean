m=Module.new;c=Class.new;m.const_set(:C,c);old=c.name;Object.define_singleton_method(:const_added){|n|if n==:M;p [old,c.name,c.name.frozen?,c.name.equal?(c.name)];end};M=m
