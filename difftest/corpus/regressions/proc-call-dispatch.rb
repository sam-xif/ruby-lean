# L272 / ratchet F51: native Proc calls participate in ordinary method lookup.
f = lambda { 1 }
p [f.call, f[], f.yield, f.()]
class << f
  alias original call
  def call; 7; end
end
p [f.call, f.original, f[]]

pattern = proc { |x| 1 }
def pattern.call(x); 7; end
p [pattern.call(0), pattern[0], pattern.yield(0), pattern === 0]

g = lambda { 2 }
def g.call; super + 1; end
p g.call

h = lambda { 3 }
class << h
  private :call
end
begin
  h.call
rescue NoMethodError
  p :private
end
p h.send(:call)
begin
  h.public_send(:call)
rescue NoMethodError
  p :public_send_private
end

j = lambda { 4 }
class << j
  undef_method :call
  def method_missing(name, *args); 9; end
end
p j.call
p j[]

u = lambda { 4 }
class << u
  undef_method :call
end
begin
  u.call
rescue NoMethodError
  p :undefined
end

k = lambda { 5 }
def k.[]; 11; end
def k.yield; 12; end
p [k.call, k[], k.yield]
begin
  k.send(:"()")
rescue NoMethodError
  p :no_paren_method
end

class Object
  def call; 99; end
end
p lambda { 6 }.call

class Proc
  alias native_call call
  def call; 17; end
end
p [lambda { 8 }.call, lambda { 8 }.native_call]
module ProcWrapper
  def call; super + 1; end
end
class Proc
  prepend ProcWrapper
end
p lambda { 8 }.call

class Proc
  undef_method :call
end
z = lambda { 10 }
def z.call; super; end
begin
  z.call
rescue NoMethodError
  p :missing_super
end
