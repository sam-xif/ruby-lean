class TypeError;alias __l286_saved_initialize initialize;end
class ArgumentError;alias __l286_saved_initialize initialize;end
class ZeroDivisionError;alias __l286_saved_initialize initialize;end
class LocalJumpError;alias __l286_saved_initialize initialize;end
class IndexError;alias __l286_saved_initialize initialize;end
# native-type-error
$n=nil
class TypeError;def initialize(*a,**kw);p [:init,a,kw,block_given?];super;end;end;begin;1+nil;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# native-argument-error
$n=nil
class ArgumentError;def initialize(*a,**kw);p [:init,a,kw];super;end;end;def one(x);end;begin;one;rescue=>e;p [e.class,e.message];end
class ArgumentError;alias initialize __l286_saved_initialize;end
# native-zero-divide
$n=nil
class ZeroDivisionError;def initialize(*a,**kw);p [:init,a,kw];super;end;end;begin;1/0;rescue=>e;p [e.class,e.message];end
class ZeroDivisionError;alias initialize __l286_saved_initialize;end
# native-message-override
$n=nil
class TypeError;def initialize(*a);super("custom");end;end;begin;1+nil;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# native-init-raises
$n=nil
class TypeError;def initialize(*a);raise "inside";end;end;begin;1+nil;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# native-init-undef
$n=nil
class TypeError;undef initialize;end;begin;1+nil;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# current-error-during-init
$n=nil
class TypeError;def initialize(s);p $!.class;super;end;end;begin;1/0;rescue;begin;1+nil;rescue=>e;p [e.class,e.message];end;end
class TypeError;alias initialize __l286_saved_initialize;end
# local-jump
$n=nil
class LocalJumpError;def initialize(*a);p [:init,a];super;end;end;def f;yield;end;begin;f;rescue=>e;p [e.class,e.message];end
class LocalJumpError;alias initialize __l286_saved_initialize;end
# index
$n=nil
class IndexError;def initialize(*a);p [:init,a];super;end;end;begin;[].fetch(1);rescue=>e;p [e.class,e.message];end
class IndexError;alias initialize __l286_saved_initialize;end
# error-init-missing
$n=nil
class TypeError;undef initialize;def method_missing(n,*a,**kw);p [n,a,kw];end;end;begin;1+nil;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# error-init-no-super
$n=nil
class TypeError;def initialize(s);p s;99;end;end;begin;1+nil;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# error-init-alias
$n=nil
class TypeError;alias old_initialize initialize;def initialize(s);p :init;old_initialize(s);end;end;begin;1+nil;rescue=>e;p e.message;end
class TypeError;alias initialize __l286_saved_initialize;end
# error-init-super-kw
$n=nil
class TypeError;def initialize(message,**kw);p [message,kw];super(message);end;end;begin;1+nil;rescue=>e;p e.class;end
class TypeError;alias initialize __l286_saved_initialize;end
# error-init-throw
$n=nil
class TypeError;def initialize(s);throw :done,7;end;end;p catch(:done){1+nil};p :after
class TypeError;alias initialize __l286_saved_initialize;end
# error-init-ensure
$n=nil
class TypeError;def initialize(s);raise "replacement";end;end;begin;begin;1+nil;ensure;p [:ensure,$!.class];end;rescue=>e;p [e.class,e.message];end
class TypeError;alias initialize __l286_saved_initialize;end
# no-new
$n=nil
class TypeError;def self.new(*a);p :wrong;end;def self.allocate;p :wrong;end;def self.exception(*a);p :wrong;end;def initialize(s);p s;super;end;end;begin;1+nil;rescue=>e;p e.class;end
class TypeError;alias initialize __l286_saved_initialize;end
nil
