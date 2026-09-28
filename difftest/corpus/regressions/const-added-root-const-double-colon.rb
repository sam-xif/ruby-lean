class Object;def self.const_added(n);p n;end;end;::X=1;Object.const_set("Y",2);p [X,Y]
