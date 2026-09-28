m=Module.new;c=Class.new;m.const_set(:C,c);done=false;Object.define_singleton_method(:const_added){|n|if n==:M && !done;done=true;Object.const_set(:M,7);end};M=m;p [M,m.name,c.name]
