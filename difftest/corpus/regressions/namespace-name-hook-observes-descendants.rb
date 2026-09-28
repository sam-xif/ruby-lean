m=Module.new;c=Class.new;m.const_set(:C,c);Object.define_singleton_method(:const_added){|n|p [n,m.name,c.name] if n==:M};M=m
