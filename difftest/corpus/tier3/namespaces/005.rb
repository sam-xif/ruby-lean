module Outer
  VAL = "outer"
  module Inner
    VAL = "inner"
    def self.a; VAL; end
  end
  def self.b; VAL; end
  def self.c; Inner::VAL; end
end
puts Outer::Inner.a
puts Outer.b
puts Outer.c
puts defined?(Outer::Inner::VAL)
Outer::Inner::VAL
