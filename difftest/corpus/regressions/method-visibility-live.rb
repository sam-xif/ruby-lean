# L282: method visibility live.

# visibility-inherited-live
module Case0
  class VP;def x;1;end;end
  class VC<VP;private :x;end
  p VC.new.send(:x)
  class VP;def x;2;end;end
  p VC.new.send(:x)
  class VC;public :x;end
  p VC.new.x
  class VP;def x;3;end;end
  p VC.new.x
end

# visibility-module-inherited
module Case1
  module VBase;def x;1;end;end
  module VChild;include VBase;private :x;end
  class VUse;include VChild;end
  p VUse.new.send(:x)
  module VBase;def x;2;end;end
  p VUse.new.send(:x)
  module VF;public :puts;end
  p VF.public_method_defined?(:puts)
  class VO;include VF;end
  VO.new.puts('public')
end

# macro-module-fallback
module Case2
  module MF;alias_method :echo,:puts;private :puts;public :echo;end;class FC;include MF;end;FC.new.echo('ok');p MF.private_method_defined?(:puts)
end

# visibility-strings
module Case3
  class VC;def x;end;p private('x');p public('x');end;module VM;def x;end;p module_function('x');end
end

# initializer-visibility
module Case4
  class IV
   [:initialize,:initialize_copy,:initialize_dup,:initialize_clone].each do |n|
   define_method(n){};p [:def,n,private_method_defined?(n)]
   attr_reader(n);p [:attr,n,private_method_defined?(n)]
   define_singleton_method(n){};p [:single,n,respond_to?(n)]
   end
   def foo;end
   alias initialize foo
   p private_method_defined?(:initialize)
   private
   define_method(:hidden){};p private_method_defined?(:hidden)
   class << self;def initialize;end;end
   p respond_to?(:initialize)
  end
end

class LiveBase
  def item; 1; end
end
class LiveChild < LiveBase
  private :item
  alias snapshot item
end
class LiveBase
  def item; 2; end
end
p [LiveChild.new.send(:item), LiveChild.new.send(:snapshot)]
class LiveBase
  undef item
end
p [LiveChild.private_method_defined?(:item), LiveChild.new.respond_to?(:item), LiveChild.new.respond_to?(:item, true)]
p LiveChild.new.instance_eval { defined?(item) }
begin
  LiveChild.alias_method(:broken, :item)
rescue NameError => e
  p e.message
end
LiveChild.send(:public, :item)
p [LiveChild.public_method_defined?(:item), LiveChild.new.respond_to?(:item), defined?(LiveChild.new.item)]
begin
  LiveChild.new.send(:item)
rescue NoMethodError
  p :undefined
end
class LiveChild
  remove_method :item
end
p LiveChild.new.send(:snapshot)
module FunctionBase
  def item; 3; end
end
module FunctionCopy
  include FunctionBase
  module_function :item
end
module FunctionBase
  def item; 4; end
end
class FunctionHost
  include FunctionCopy
end
p [FunctionCopy.item, FunctionHost.new.send(:item)]
