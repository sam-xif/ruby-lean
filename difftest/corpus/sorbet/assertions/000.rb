# typed: true
require "sorbet-runtime"

x = T.let(1, Integer)
puts x + 1
