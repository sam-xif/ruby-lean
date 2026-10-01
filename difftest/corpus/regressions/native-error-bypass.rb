class NameError;alias __l286_saved_initialize initialize;end
class NoMethodError;alias __l286_saved_initialize initialize;end
class KeyError;alias __l286_saved_initialize initialize;end
# native-no-method
$n=nil
class NoMethodError;def initialize(*a,**kw);p [:init,a.map{|x|x.class},a[1],a[2],a[3],kw];super;end;end;begin;Object.new.missing(1,k:2);rescue=>e;p [e.class,e.message];end
class NoMethodError;alias initialize __l286_saved_initialize;end
# native-constant
$n=nil
class NameError;def initialize(*a,**kw);p [:init,a.map{|x|x.class},a[1],kw];super;end;end;begin;MissingConstant;rescue=>e;p [e.class,e.message];end
class NameError;alias initialize __l286_saved_initialize;end
# key
$n=nil
class KeyError;def initialize(*a,**kw);p [:init,a,kw];super;end;end;begin;{}.fetch(:x);rescue=>e;p [e.class,e.message];end
class KeyError;alias initialize __l286_saved_initialize;end
nil
