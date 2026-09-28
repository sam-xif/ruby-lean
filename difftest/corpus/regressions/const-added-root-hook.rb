class Object;def self.const_added(n);p [:root,n];end;end;A=1;class C;p :class;end;module M;p :module;X=2;end;p [A,C.name,M::X]
