# init-method-missing
class CPart0;undef initialize;def method_missing(n,*a,**kw,&b);p [n,a,kw,b.call];:other;end;end;c=CPart0.new(2,k:3){4};p c.class

# mm-keywords-ordinary
class CPart1;def method_missing(n,*a,**kw,&b);p [n,a,kw,b.call];end;private;def hidden;end;end;c=CPart1.new;c.missing(1,k:2){3};c.hidden(4,k:5){6}

# mm-keywords-super
class CPart2;def x(*a,**kw);super;end;def method_missing(n,*a,**kw);p [n,a,kw];end;end;CPart2.new.x(1,k:2)

nil
