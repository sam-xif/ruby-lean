# L288: for captured method.

# for-instance-eval
class EForCase0;def each(&b);$b=b;end;end;for x in EForCase0.new;p [self.class,x];end;p Object.new.instance_exec(7,&$b);p x

# for-dm
class EForCase1;def each(&b);$b=b;end;end;for x in EForCase1.new;p [self.class,x];:done;end;class CForCase1;end;CForCase1.send(:define_method,:f,&$b);p CForCase1.new.f(7);p x;begin;CForCase1.new.f;rescue=>e;p [e.class,e.message];end

# for-dm-return
class EForCase2;def each(&b);$b=b;end;end;def f;for x in EForCase2.new;return x;end;end;f;class CForCase2;end;CForCase2.send(:define_method,:f,&$b);p CForCase2.new.f(7)

# for-dm-multiple
class EForCase3;def each(&b);$b=b;end;end;for x,y in EForCase3.new;[self.class,x,y];end;class CForCase3;end;CForCase3.send(:define_method,:f,&$b);p CForCase3.new.f(1,2);p [x,y];p CForCase3.new.f([3,4]);p [x,y]

# for-dm-break
class EForCase4;def each(&b);$b=b;end;end;for x in EForCase4.new;break x;end;class CForCase4;end;CForCase4.send(:define_method,:f,&$b);begin;p CForCase4.new.f(7);rescue=>e;p [e.class,e.message];end;p x

# for-dm-redo
class EForCase5;def each(&b);$b=b;end;end;n=0;for x in EForCase5.new;n+=1;x+=10;p [n,x];redo if n==1;x;end;class CForCase5;end;CForCase5.send(:define_method,:f,&$b);p CForCase5.new.f(7);p x

# for-dm-next
class EForCase6;def each(&b);$b=b;end;end;for x in EForCase6.new;next x+1;end;class CForCase6;end;CForCase6.send(:define_method,:f,&$b);p CForCase6.new.f(7);p x

nil
