module N;end;class Object;def self.inherited(c);p [c.name,N.const_defined?(:C,false)];end;end;class N::C;p :body;end
