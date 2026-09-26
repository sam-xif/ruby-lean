# Array has its own live map/collect; Enumerable's implementation calls each.
[:map, :collect].each do |method|
  xs = [1, 2]
  def xs.each; yield 99; end
  def xs.length; 0; end
  def xs.[](i); 99; end
  p xs.send(method) { |x| x * 10 }

  xs = [1, 2]
  p xs.send(method) { |x| xs << 3 if x == 2; x * 10 }
  xs = [1, 2, 3]
  p xs.send(method) { |x| xs.pop if x == 1; x * 10 }
  xs = [1, 2, 3]
  p xs.send(method) { |x| xs.shift if x == 1; x * 10 }
  xs = [1, 2, 3]
  p xs.send(method) { |x| xs[1] = 7 if x == 1; x * 10 }
  xs = [1, 2]
  original = xs
  p original.send(method) { |x| xs = [9]; x * 10 }
  p [original, xs]

  p [].send(method) { raise "must not yield" }
  p [1, 2].freeze.send(method) { |x| x.to_s }
  p [1, 2].send(method) { |x| next 99 if x == 1; x }
  p [1, 2].send(method) { |x| break 42 if x == 2; x }
  xs = [1, 2]
  again = true
  p xs.send(method) { |x|
    if again
      again = false
      xs[0] = 9
      xs << 3
      redo
    end
    x * 10
  }
  begin
    [1, 2].send(method) { |x| raise "body" if x == 2; x }
  rescue => e
    p [e.class, e.message]
  end
  begin
    [1].send(method, 7) { |x| x }
  rescue => e
    p [e.class, e.message]
  end
  begin
    [1].send(method, key: 7)
  rescue => e
    p [e.class, e.message]
  end
end

def return_from_map
  [1, 2].map { |x| return x + 40 if x == 2; x }
  :unreachable
end
p return_from_map
p [1, 2].map { |x| [3, 4].map { |y| x + y } }

class NativeMapArray < Array
  def each; yield 99; end
  def map; super; end
end
xs = NativeMapArray.new(0)
xs << 1 << 2
p xs.map { |x| x + 1 }
p xs.collect { |x| x + 1 }
p xs.map { |x| x }.class

xs = [1, 2]
class << xs
  alias saved_map map
  def map; [:override]; end
end
p xs.map { |x| x }
p xs.saved_map { |x| x + 1 }
p xs.collect { |x| x + 1 }
class << xs
  private :collect
end
begin
  xs.collect { |x| x }
rescue NoMethodError
  p :private
end
p xs.send(:collect) { |x| x + 1 }
class << xs
  undef saved_map
  def method_missing(name, *args); :missing; end
end
p xs.saved_map { |x| x }

module MapWrapper
  def map; super; end
end
class WrappedMapArray < Array
  prepend MapWrapper
  def each; yield 99; end
end
xs = WrappedMapArray.new(0)
xs << 1 << 2
p xs.map { |x| x + 1 }

class CustomEnumerable
  include Enumerable
  def each; yield 7; yield 8; end
end
p CustomEnumerable.new.map { |x| x + 1 }
p CustomEnumerable.new.collect { |x| x + 1 }

# Removing Array's own entry exposes Enumerable; undef must stop the lookup.
class Array
  remove_method :map
end
xs = [1, 2]
def xs.each; yield 99; end
p xs.map { |x| x + 1 }
class Array
  undef collect
end
begin
  [1].collect { |x| x }
rescue NoMethodError
  p :undefined
end
