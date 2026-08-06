# typed: true
require "sorbet-runtime"

def apply(f, x)
  f.call(x)
end

def call_missing(obj)
  obj.no_such_method
end

puts apply(->(n) { n + 1 }, 1)
puts call_missing(3)
