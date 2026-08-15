# C37. A range or regex literal consults **no constant** in Ruby — it is a parser
# node. The desugarer lowered both to a send over a bare `Range`/`Regexp`
# constant, which reintroduced a lexical lookup Ruby never performs, so any
# enclosing constant of that name hijacked every literal in the scope.
#
# The prelude's own sorbet shim defines `T::Range`, so this was live for every
# range literal inside `module T` — found writing L127's truncation helper.
module Shadowed
  Range = 5
  Regexp = 5

  def self.range_literal = (1..2)
  def self.exclusive = (1...3).to_a
  # `.begin`, not `.first(2)`: `Range#first` with an argument is unmodeled, and a
  # gate anywhere would hide every line of this file
  def self.endless = (1..).begin
  def self.slice = "abcdef"[1..3]
  def self.regex_literal = ("ab" =~ /b/)
  def self.regex_interp = ("ab" =~ /#{"b"}/)
  def self.case_range = (case 5 when 1..9 then "in" else "out" end)
end

puts(Shadowed.range_literal.inspect)
puts(Shadowed.exclusive.inspect)
puts(Shadowed.endless.inspect)
puts(Shadowed.slice.inspect)
puts(Shadowed.regex_literal.inspect)
puts(Shadowed.regex_interp.inspect)
puts(Shadowed.case_range.inspect)

# the constants themselves are untouched — the literal simply does not read them
puts(Shadowed::Range.inspect)
puts(Shadowed::Regexp.inspect)

# and a literal outside the shadow still works
puts((1..2).inspect)
puts(("ab" =~ /b/).inspect)
