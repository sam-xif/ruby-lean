# boot-exception-class
[Exception,StandardError,RuntimeError,TypeError,ArgumentError,NameError,NoMethodError].each{|k|begin;raise k,"msg";rescue Exception=>e;p [e.class,e.message];end}

# anonymous-exception-class
ECase1=Class.new(StandardError);begin;raise ECase1,"msg";rescue=>e;p [e.class,e.message];end

# new-anonymous-singleton-inheritance
class PCase2;def self.x;7;end;end;c=Class.new(PCase2);p c.x

# exception-class
class ECase3<StandardError;def initialize(s);p [:init,s];super;end;end;p ECase3.exception("msg").message

# exception-class-block
class ECase4<StandardError;def initialize(*a,&b);p [a,block_given?,b.call];super(*a);end;end;p ECase4.exception("msg"){1}.message

# specialized-super
class Exception;def initialize(*a);p a;7;end;end;[NameError,NoMethodError,KeyError,FrozenError].each{|k|e=k.allocate;p e.send(:initialize).equal?(e);p e.send(:initialize,"x").equal?(e)}

nil
