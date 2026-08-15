# L123. `rb_check_funcall`'s callability rule decides whether `coerce` is even
# tried: a user `respond_to?` is believed, a user `respond_to_missing?` vetoes
# the `method_missing` route, a `respond_to?` that says true over a method
# nobody supplies is still not callable, and `private`/singleton/`prepend`/module
# definitions all count.
class Liar
  def coerce(other) = [1, 2]

  def respond_to?(name, include_all = false) = false

  def inspect = "#<Liar>"
end

class Yes
  def respond_to?(name, include_all = false) = true

  def inspect = "#<Yes>"
end

class Rtm
  def method_missing(name, *args) = [7, 8]

  def respond_to_missing?(name, include_all) = (name == :coerce)

  def inspect = "#<Rtm>"
end

class NoRtm
  def method_missing(name, *args) = [7, 8]

  def respond_to_missing?(name, include_all) = false

  def inspect = "#<NoRtm>"
end

class Priv
  def coerce(other) = [1, 2]
  private :coerce

  def inspect = "#<Priv>"
end

module Coercible
  def coerce(other) = [other, 2]
end

class ViaModule
  include Coercible
end

module Pre
  def coerce(other) = [other, 100]
end

class Prepended
  prepend Pre
end

[Liar.new, Yes.new, Rtm.new, NoRtm.new, Priv.new, ViaModule.new, Prepended.new].each do |o|
  begin
    puts(0 + o)
  rescue StandardError => e
    puts("#{e.class}: #{e.message}")
  end
end

o = Object.new
def o.coerce(other)
  [other, 9]
end
puts(5 + o)

class NilClass
  def coerce(other) = [other, 0]
end
puts(5 + nil)
puts((5 < nil).inspect)
puts("end")
