m=Module.new;c=Class.new;m.const_set(:C,c);old=c.name;Object.define_singleton_method(:const_added){|n|raise "hook" if n==:M};begin;M=m;rescue=>e;p [e.message,old,c.name,c.name.equal?(c.name)];end
