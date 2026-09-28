# L288: for control flow.

# for-block-return
a=[1,2];def a.each;yield 7;:finished;end;p(for x in a;break :stopped;end);p x

# for-return-ensure
class EForCase1;def each;begin;yield 7;ensure;p :each_ensure;end;end;end;def f;begin;for x in EForCase1.new;return x;end;ensure;p :method_ensure;end;end;p f

# for-break-ensure
class EForCase2;def each;begin;yield 7;yield 8;ensure;p :each_ensure;end;end;end;p(for x in EForCase2.new;begin;break x;ensure;p :body_ensure;end;end)

# for-next-result
class EForCase3;def each;p yield(1);p yield(2);:done;end;end;p(for x in EForCase3.new;next x+7;end)

# for-redo-binding
class EForCase4;def each;p :each;yield 1;yield 2;:done;end;end;n=0;p(for x in EForCase4.new;n+=1;x+=10;p [x,n];redo if n==1;end);p x

# for-throw
class EForCase5;def each;begin;yield 7;ensure;p :each_ensure;end;end;end;p catch(:done){for x in EForCase5.new;throw :done,x;end}

# for-collection-break
p(while true;for x in (true ? (break :outer) : []);p :wrong;end;end)

# for-escaped-return
class EForCase7;def each(&b);$saved=b;:saved;end;end;def f;for x in EForCase7.new;return x;end;:finished;end;p f;begin;p $saved.call(7);rescue=>e;p [e.class,e.message];end

# for-escaped-break
class EForCase8;def each(&b);$saved=b;:saved;end;end;p(for x in EForCase8.new;break x;end);begin;p $saved.call(7);rescue=>e;p [e.class,e.message];end;p x

nil
