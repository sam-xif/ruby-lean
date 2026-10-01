class Symbol;def to_str;raise "wrong";end;def to_s;raise "wrong";end;def inspect;raise "wrong";end;end;p Module.new.const_set(:X,1)
