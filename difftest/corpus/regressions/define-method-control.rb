# L288: define method control.

# dm-closed-break
class CForCase0;define_method(:f){break 7};end;p CForCase0.new.f

# dm-closed-next
class CForCase1;define_method(:f){next 7};end;p CForCase1.new.f

# dm-redo
n=0;class CForCase2;end;CForCase2.send(:define_method,:f){|x|n+=1;x+=10;p [n,x];redo if n==1;x};p CForCase2.new.f(7)

# dm-redo-destructure
class PairForCase3;def to_ary;p :convert;[7];end;end;n=0;class CForCase3;end;CForCase3.send(:define_method,:f){|(x)|n+=1;x+=10;p [n,x];redo if n==1;x};p CForCase3.new.f(PairForCase3.new)

# dm-break-ensure
class CForCase4;define_method(:f){begin;break 7;ensure;p :ensure;end};end;p CForCase4.new.f

# dm-lambda-break
class CForCase5;end;CForCase5.send(:define_method,:f,&->(x){break x+1});p CForCase5.new.f(7)

# dm-super-implicit
class AForCase6;def f;7;end;end;class BForCase6<AForCase6;define_method(:f){super};end;begin;p BForCase6.new.f;rescue=>e;p [e.class,e.message];end

# dm-super-explicit
class AForCase7;def f;7;end;end;class BForCase7<AForCase7;define_method(:f){super()};end;p BForCase7.new.f

nil
