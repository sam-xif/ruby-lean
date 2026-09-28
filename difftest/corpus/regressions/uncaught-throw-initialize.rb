class ArgumentError;alias __l286_saved_initialize initialize;end
class UncaughtThrowError;alias __l286_saved_initialize initialize;end
# uncaught-default
$n=nil
begin;throw :tag,7;rescue=>e;p [e.class,e.message,e.tag,e.value];p e;end

# uncaught-lazy-inspect
$n=nil
o=Object.new;def o.inspect;p :inspect;"TAG";end;begin;throw o,9;rescue=>e;p :rescued;p [e.tag.equal?(o),e.value];p e.message;p e.message;end

# uncaught-init-raises
$n=nil
class UncaughtThrowError;def initialize(*a);p a;raise "replacement";end;end;begin;throw :tag,4;rescue=>e;p [e.class,e.message];end
class UncaughtThrowError;alias initialize __l286_saved_initialize;end
# uncaught-init-alias
$n=nil
class UncaughtThrowError;alias old initialize;def initialize(*a);p a;old(*a);end;end;begin;throw :tag,4;rescue=>e;p [e.class,e.message,e.tag,e.value];end
class UncaughtThrowError;alias initialize __l286_saved_initialize;end
# uncaught-super-custom
$n=nil
class ArgumentError;def initialize(*a);p a;super;end;end;begin;throw :tag,4;rescue=>e;p [e.message,e.tag,e.value];end
class ArgumentError;alias initialize __l286_saved_initialize;end
# uncaught-raw-fixed
$n=nil
e=UncaughtThrowError.new(:tag,4,"constant");p [e.message,e.tag,e.value];p e.send(:initialize,:other,8,"changed").equal?(e);p [e.message,e.tag,e.value]

# uncaught-inspect-nonstr
$n=nil
o=Object.new;def o.inspect;9;end;begin;throw o;rescue=>e;p e.message;end

# uncaught-inspect-convert
$n=nil
o=Object.new;def o.inspect;x=Object.new;def x.to_s;"TAG";end;x;end;begin;throw o;rescue=>e;p e.message;end

# uncaught-throw
$n=nil
class UncaughtThrowError;def initialize(*a);p [:init,a];super;end;end;begin;throw :tag,7;rescue=>e;p [e.class,e.message];end
class UncaughtThrowError;alias initialize __l286_saved_initialize;end
# uncaught-copy
$n=nil
e=UncaughtThrowError.new(:tag,4,"uncaught throw %p");[e.dup,e.clone,e.exception("changed")].each{|f|p [f.message,f.tag,f.value]};nil

nil
