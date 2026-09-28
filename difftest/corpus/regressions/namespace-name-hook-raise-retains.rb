m=Module.new;c=Class.new;m.const_set(:C,c);Object.define_singleton_method(:const_added){|n|raise "hook" if n==:M};begin;M=m;rescue=>e;p [e.message,m.name,c.name,M.equal?(m)];end
