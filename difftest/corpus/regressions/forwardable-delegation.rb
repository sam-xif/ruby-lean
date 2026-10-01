# forward-load-all
module Forwardable
 def self.method_added(n);p [:added,n];end
 def self.singleton_method_added(n);p [:single,n];end
end
module SingleForwardable
 def self.method_added(n);p [:added_single,n];end
end
p require('forwardable')
p [Forwardable::VERSION,Forwardable::VERSION.frozen?,Forwardable::FORWARDABLE_VERSION.equal?(Forwardable::VERSION),Forwardable.debug]
Forwardable.debug=3;p Forwardable.debug

# forward-args
require 'forwardable'
class Inner
 def run(x,k:,**kw,&b);[x,k,kw,b.call(x)];end
end
class Wrapper
 extend Forwardable
 def initialize;@inner=Inner.new;end
 p def_delegator(:@inner,:run,:go)
end
p Wrapper.new.go(2,k:3,z:4){|v|v+10}

# forward-single
require 'forwardable'
a=Object.new;a.instance_variable_set(:@list,[1,2]);a.extend SingleForwardable
p a.def_delegators(:@list,:size,:first,:__send__, :__id__)
p [a.size,a.first]
module Wrap
 extend SingleForwardable
 def self.inner;[3,4];end
 p def_delegator(:inner,:first)
end
p Wrap.first

# forward-method-hooks
require 'forwardable'
class C
 extend Forwardable
 def self.method_added(n);p n;end
 def initialize;@list=[1,2];end
 p def_delegators(:@list,:size,:first)
end
p [C.new.size,C.new.first]

# forward-constant
require 'forwardable'
module Box;DATA=[8,9];end
class C
 extend Forwardable
 p delegate({[:first,:size]=>'Box::DATA'})
end
p [C.new.first,C.new.size]

# forward-override-helper
require 'forwardable'
def Forwardable._delegator_method(*a)
 p a[1..3]
 proc { def generated;7;end }
end
class C
 extend Forwardable
 p def_delegator(:@whatever,:size)
end
p C.new.generated
