class FrozenError;alias __l286_saved_initialize initialize;end
# native-frozen
$n=nil
class FrozenError;def initialize(*a,**kw);p [:init,a,kw];super;end;end;begin;[1].freeze<<2;rescue=>e;p [e.class,e.message];end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-order
$n=nil
class FrozenError;def initialize(s);p [:init,s];super;end;end;o=Object.new;def o.inspect;p :inspect;"OBJECT";end;o.freeze;begin;o.instance_variable_set(:@x,1);rescue=>e;p e.message;end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-custom-message
$n=nil
class FrozenError;def initialize(s);p s;super("CUSTOM");end;end;begin;[1].freeze<<2;rescue=>e;p e.message;end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-init-raises
$n=nil
class FrozenError;def initialize(s);raise "inside";end;end;o=Object.new;def o.inspect;p :inspect;"OBJECT";end;o.freeze;begin;o.instance_variable_set(:@x,1);rescue=>e;p [e.class,e.message];end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-live-prefix
$n=nil
class FrozenError;def initialize(s);$prefix=s;super;end;end;o=Object.new;def o.inspect;$prefix << "changed:";"OBJECT";end;o.freeze;begin;o.instance_variable_set(:@x,1);rescue=>e;p e.message;end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-prefix-freeze
$n=nil
class FrozenError;def initialize(s);$n=($n||0)+1;s.freeze if $n==1;super;end;end;begin;[1].freeze<<2;rescue=>e;p [$n,e.class,e.message];end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-exc-freeze-once
$n=nil
class FrozenError;def initialize(s);$n=($n||0)+1;super;freeze if $n==1;end;end;begin;[1].freeze<<2;rescue=>e;p [$n,e.class,e.message];end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-prefix-shared
$n=nil
class FrozenError;def initialize(s);$prefix=s;super(s);end;end;begin;[1].freeze<<2;rescue=>e;p [e.message.equal?($prefix),$prefix];end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-append-no-send
$n=nil
class FrozenError;def initialize(s);def s.<<(x);raise "wrong";end;super;end;end;begin;[1].freeze<<2;rescue=>e;p e.message;end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-nil-message
$n=nil
class FrozenError;def initialize(s);super(nil);end;end;begin;[1].freeze<<2;rescue=>e;p e.message;end
class FrozenError;alias initialize __l286_saved_initialize;end
# frozen-order-class
$n=nil
class Array;def self.to_s;p :class;"ARRAY";end;end;class FrozenError;def initialize(s);p [:init,s];super;end;end;begin;[1].freeze<<2;rescue=>e;p e.message;end
class FrozenError;alias initialize __l286_saved_initialize;end
nil
