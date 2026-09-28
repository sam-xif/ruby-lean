module M;def self.const_added(n);p [:M,n];end;end;class Object;def self.const_added(n);p [:root,n];end;end;M.module_eval {X=1};M.class_exec {Y=2};p [X,Y,M.const_defined?(:X,false)]
