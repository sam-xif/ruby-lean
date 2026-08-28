#!/usr/bin/env ruby
# frozen_string_literal: true

# require_strip.rb — drop toplevel `require`/`require_relative` statements.
#
# Part of the certificate strip pipeline (sig_strip | visibility_strip |
# freeze_strip | require_strip). Sound for the *standalone-file boot*
# certificate target: the J-certificate certifies one file's boot, and a
# `require` only matters if the booted statements dereference the loaded
# constants — which the M0 measurement (homebrew/m0.rb) shows they don't in
# the slice files (cross-file references live inside def bodies, dead at
# boot). NOT semantics-preserving for whole-program runs; the whole-slice
# certificate story re-introduces the load order as file concatenation.
require "prism"

src = $stdin.read
result = Prism.parse(src)
edits = []
finder = Class.new(Prism::Visitor) do
  define_method(:visit_call_node) do |node|
    if node.receiver.nil? && %w[require require_relative].include?(node.name.to_s) &&
       node.arguments&.arguments&.length == 1 &&
       node.arguments.arguments[0].is_a?(Prism::StringNode)
      edits << [node.location.start_offset, node.location.end_offset]
    end
    super(node)
  end
end.new
result.value.accept(finder)
out = src.dup
edits.sort_by! { |(s, _)| -s }
edits.each { |(s, e)| out[s...e] = "" }
out = out.lines.map { |l| l.strip.empty? && !l.empty? ? "\n" : l }.join
print out
