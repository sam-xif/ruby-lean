# raise-undef-init
class ECase0<StandardError;undef initialize;end;begin;raise ECase0;rescue Exception=>e;p [e.class,e.message];end

# raise-init-missing
class ECase1<StandardError;undef initialize;def method_missing(n,*a);p [n,a];end;end;begin;raise ECase1,"msg";rescue Exception=>e;p [e.class,e.message];end

# raise-new-override
class ECase2<StandardError;def self.new(*a);raise "wrong";end;def initialize(*a);p a;super;end;end;begin;raise ECase2,"msg";rescue Exception=>e;p [e.class,e.message];end

# raise-exception-override
class ECase3<StandardError;def self.exception(*a);p a;RuntimeError.new("replacement");end;end;begin;raise ECase3,"msg";rescue Exception=>e;p [e.class,e.message];end

# raise-exception-arity
class ECase4<StandardError;def self.exception(*a);p a;super;end;end;begin;raise ECase4;rescue Exception=>e;p [e.class,e.message];end;begin;raise ECase4,"msg";rescue Exception=>e;p [e.class,e.message];end

# raise-exception-duck
o=Object.new;def o.exception(*a);p a;RuntimeError.new("duck");end;begin;raise o,"msg";rescue Exception=>e;p [e.class,e.message];end

# raise-exception-private
class ECase6<StandardError;def self.exception(*a);p :hook;super;end;private_class_method :exception;end;begin;raise ECase6;rescue Exception=>e;p [e.class,e.message];end

# raise-exception-undef
class ECase7<StandardError;class<<self;undef exception;end;end;begin;raise ECase7;rescue Exception=>e;p [e.class,e.message];end

# raise-exception-bad
o=Object.new;def o.exception;7;end;begin;raise o;rescue Exception=>e;p [e.class,e.message];end

# raise-failed-init
class ECase9<StandardError;def initialize;raise "inside";end;end;begin;raise ECase9;rescue Exception=>e;p [e.class,e.message];end

# raise-string-two
begin;raise "first","second";rescue=>e;p [e.class,e.message];end

# raise-alias
alias failer raise;class ECase11<StandardError;def self.exception;RuntimeError.new("hook");end;end;begin;failer ECase11;rescue=>e;p [e.class,e.message];end

# raise-instance-override
e=RuntimeError.new("old");def e.exception(*a);p a;RuntimeError.new("new");end;begin;raise e;rescue=>x;p [x.class,x.message];end

# raise-reraise-hook
e=RuntimeError.new("original");def e.exception;RuntimeError.new("hook");end;begin;raise "outer";rescue;begin;raise;rescue=>x;p x.message;end;end

# raise-fail
begin;fail TypeError,"msg";rescue=>e;p [e.class,e.message];end

# raise-custom-runtime-init
class RuntimeError;def initialize(*a);p [:init,a];super;end;end;begin;raise "msg";rescue=>e;p e.message;end;begin;raise;rescue=>e;p e.message;end

nil
