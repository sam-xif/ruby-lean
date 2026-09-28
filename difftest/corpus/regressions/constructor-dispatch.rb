# undef-init
class CPart0;undef initialize;end;begin;CPart0.new;rescue=>e;p [e.class,e.message];end

# inherited-undef-init
class PPart1;undef initialize;end;class CPart1<PPart1;end;begin;CPart1.new;rescue=>e;p [e.class,e.message];end

# init-private-method-missing
class CPart2;undef initialize;private;def method_missing(n,*a);p [n,a];end;end;p CPart2.new(1).class

# builtin-init-alias
class CPart3;alias initialize p;end;p CPart3.new(2).class

# alias-new
class CPart4;attr_reader :x;def initialize(x);@x=x;end;class<<self;alias make new;end;end;p CPart4.make(3).x

# new-super
class CPart5;attr_reader :x;def initialize(x);@x=x;end;def self.new(x);super(x+1);end;end;p CPart5.new(3).x

# new-private
class CPart6;def initialize;p :init;end;private_class_method :new;end;begin;CPart6.new;rescue=>e;p [e.class,e.message];end;p CPart6.send(:new).class

# allocate-override
class CPart7;def self.allocate;raise "wrong";end;end;p CPart7.new.class

# constructor-allocate-alias
class CPart8;class<<self;alias reserve allocate;end;def initialize;raise "bad";end;end;p CPart8.reserve.class

# allocator-private
class CPart9;private_class_method :allocate;class<<self;alias build allocate;end;end;begin;CPart9.allocate;rescue=>e;p [e.class,e.message];end;p CPart9.send(:build).class

# initialize-public
class CPart10;def initialize;p :init;end;public :initialize;end;p CPart10.new.initialize

nil
