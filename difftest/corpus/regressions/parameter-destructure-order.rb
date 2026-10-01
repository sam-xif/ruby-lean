# method-default-order
o=Object.new;def o.to_ary;p :convert;[1,2];end;def f((a,b),c=(p :default));p [a,b,c];end;f(o)

# default-names
def f((a,b),c=(p [:default,a,b]),k:(p [:key,a,b]));p [a,b,c,k];end;f([1,2])

# default-assign
def f((a,b),c=(a=9));p [a,b,c];end;f([1,2])

# post-convert
o=Object.new;def o.to_ary;p :convert;[1,2];end;def f(a=(p :default),*r,(b,c));p [a,r,b,c];end;f(o)

# nested-snapshot
$a=[];o=Object.new;def o.to_ary;p :convert;$a[1]=9;$a<<10;[1,2];end;$a=[o,3,4];def f(((a,b),*r,c));p [a,b,r,c];end;f($a);p $a[1]

# cross-parameter-live
$a=[3,4];o=Object.new;def o.to_ary;$a[0]=9;[1,2];end;def f((a,b),(c,d));p [a,b,c,d];end;f(o,$a)

# define-method-default
a=99;b=98;class CBindingCase6;end;CBindingCase6.send(:define_method,:f){|(a,b),c=(p [:default,a,b])|p [a,b,c]};CBindingCase6.new.f([1,2]);p [a,b]

# bind-keyword-mutation
a=[1,2];def f((a,b),k:(p :keyword;$a[0]=9));p [a,b,k];end;$a=a;f(a)

# bind-symbol-slot-collision
def f((a,b),__destr_0);p [a,b,__destr_0];end;f([1,2],9)

# bind-default-local-collision
def f((a,b),c=(__destr_0=8));p [a,b,c,__destr_0];end;f([1,2])

# dm-destructure-shadow
a=99;b=98;c=97;class CBindingCase10;end;CBindingCase10.send(:define_method,:f){|(a,(b,c))|p [a,b,c]};CBindingCase10.new.f([1,[2,3]]);p [a,b,c]

# method-alias-destructure
class CBindingCase11;def f((a,b));p [a,b];end;alias g f;def f(x);p :wrong;end;end;CBindingCase11.new.g([1,2])

# optional-raise
begin;o=Object.new;def o.to_ary;p :wrong;[1,2];end;def f((a,b),c=(raise "done"));p :wrong;end;p f(o);rescue=>err;p [err.class,err.message];end

nil
