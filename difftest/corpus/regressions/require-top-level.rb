module Loader; def self.load_it; require 'sorbet-runtime'; end;end
p Loader.load_it
p [T.class,Loader.const_defined?(:T,false),require('sorbet-runtime')]
p T.let(1,Integer)
class ClassLoader
  def self.load_it
    require 'sorbet-runtime'
    p [const_defined?(:T, false), const_defined?(:T)]
  end
end
ClassLoader.load_it
