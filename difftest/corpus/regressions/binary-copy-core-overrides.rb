class String;def dup;raise "wrong";end;def clone;raise "wrong";end;def initialize(*a);raise "wrong";end;end;s=255.chr;t=s.b;p [t.bytes,t.equal?(s),t.frozen?]
