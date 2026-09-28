# exception-nil
[nil,"",1].each{|x|e=RuntimeError.new(x);p [e.message,e.to_s,e.inspect]}

# exception-live-message
o=Object.new;def o.to_s;@msg||"one";end;e=RuntimeError.new(o);p e.message;o.instance_variable_set(:@msg,"two");p e.message

# exception-string-identity
s="one";e=RuntimeError.new(s);p e.to_s.equal?(s);s << "two";p [e.message,e.inspect];f=e.exception(s);p [f.to_s.equal?(s),f.equal?(e)]

# exception-array-inspect
class MsgCase3;def inspect;"CUSTOM";end;end;e=RuntimeError.new([MsgCase3.new]);p e.message;p e.inspect

# exception-hash-inspect
class MsgCase4;def inspect;"CUSTOM";end;end;e=RuntimeError.new({a:MsgCase4.new});p e.message;p e.inspect

# exception-array-to-s
a=[];def a.to_s;"CUSTOM";end;e=RuntimeError.new(a);p e.message;p e.inspect

# exception-string-to-s
s="raw";def s.to_s;"WRONG";end;e=RuntimeError.new(s);p [e.message,e.inspect,e.message.equal?(s)]

# exception-message-bad-to-s
o=Object.new;def o.to_s;7;end;e=RuntimeError.new(o);begin;p e.message;rescue=>err;p [err.class,err.message];end

# exception-default-class-override
e=RuntimeError.new(nil);def e.class;String;end;p [e.message,e.to_s]

# message-converter-order
o=Object.new;def o.to_str;p :to_str;"str";end;def o.to_s;p :wrong;"str";end;p RuntimeError.new(o).message;o=Object.new;def o.respond_to?(*a);p a;false;end;def o.to_s;"wrong";end;begin;p RuntimeError.new(o).message;rescue=>e;p [e.class,e.message];end

nil
