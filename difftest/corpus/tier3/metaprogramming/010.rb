class Recorder
  def self.method_added(name)
    @seen ||= []
    @seen << name
  end

  def self.seen
    @seen
  end

  def a; 1; end
  def b; 2; end
end

p Recorder.seen
p(Recorder.class_eval { def c; 3; end })
p Recorder.seen

module Watcher
  def method_added(name)
    puts "watched #{name}"
  end
end

class Extended
  extend Watcher
  def d; end
end

class Sub < Recorder
  def e; end
end
p Sub.seen

def method_added(name)
  puts "toplevel hook ran"
end

def after_toplevel_hook; end
puts "done"
