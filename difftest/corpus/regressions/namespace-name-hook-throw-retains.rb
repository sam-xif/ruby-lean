m=Module.new;c=Class.new;m.const_set(:C,c);Object.define_singleton_method(:const_added){|n|throw :stop,9 if n==:M};p catch(:stop){M=m;:wrong};p [m.name,c.name,M.equal?(m)]
