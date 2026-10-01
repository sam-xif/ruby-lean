class P;def self.inherited(c);p c.superclass;end;end;class Class;def superclass;:fake;end;end;c=Class.new(P);p c.new.class
