class Class;undef initialize;def method_missing(n,*a);p [n,a];end;end;c=Class.new(Array);p c.class
