# raise-string-conversion
o=Object.new;def o.to_str;p :to_str;"str";end;def o.exception;p :exception;RuntimeError.new("exc");end;begin;raise o;rescue=>e;p [e.class,e.message];end

# raise-nonstring-to-str
o=Object.new;def o.to_str;p :to_str;7;end;def o.exception;p :exception;RuntimeError.new("exc");end;begin;raise o;rescue=>e;p [e.class,e.message];end

# raise-respond-hooks
o=Object.new;def o.respond_to?(n,*a);p [:response,n,a];false;end;def o.exception;RuntimeError.new("exc");end;begin;raise o;rescue=>e;p [e.class,e.message];end

# raise-mm
o=Object.new;def o.respond_to_missing?(n,*a);p [:response,n,a];true;end;def o.method_missing(n,*a);p [:missing,n,a];RuntimeError.new("mm");end;begin;raise o;rescue=>e;p [e.class,e.message];end

# raise-to-str-nil
o=Object.new;def o.to_str;p :to_str;nil;end;def o.exception(*a);p a;RuntimeError.new("exc");end;begin;raise o;rescue=>e;p e.message;end

# raise-missing-exception
o=Object.new;def o.respond_to_missing?(n,*a);n==:exception;end;def o.method_missing(n,*a);p [n,a];RuntimeError.new("missing");end;begin;raise o,"msg";rescue=>e;p e.message;end

# raise-exception-suppression
o=Object.new;def o.method_missing(n,*a);p [n,a];raise NoMethodError,"missing";end;begin;raise o,"msg";rescue=>e;p [e.class,e.message];end

nil
