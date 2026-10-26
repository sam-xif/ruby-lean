#!/usr/bin/env ruby
# frozen_string_literal: true

# The theorem is about the model. Whether the model is Ruby is a separate
# question, and this asks it of this program: it compares what the theorem
# predicts with what CRuby and the model's own binary do, on a grid of inputs.
#
#   ruby books/Books/FastPower/check.rb     # needs `make run` at the repository root
#
# For each (b, n) the two literals in ruby/fast_power.rb are replaced, the
# program is run, and it must print b ** max(n, 0) and have the value
# [b ** max(n, 0), max(n, 0).bit_length]: exactly `fast_power_correct`.
require "json"
require "open3"
require "rbconfig"

here = __dir__
source = File.read(File.join(here, "fast_power.rb"))
model = File.join(here, "../../../bin/ruby-lean")

failures = 0
cases = 0
[-7, -1, 0, 1, 2, 3, 10, 12_345_678_901_234_567_890].each do |b|
  [-3, 0, 1, 2, 3, 13, 64, 100, 255].each do |n|
    program = source.sub("Power.new(3)", "Power.new(#{b})").sub("raise_to(13)", "raise_to(#{n})")
    raise "literals not found in fast_power.rb" if program == source && [b, n] != [3, 13]

    k = [n, 0].max
    expected = [b**k, k.bit_length].inspect
    printed = "#{b**k}\n"

    cruby, = Open3.capture2(RbConfig.ruby, "-e", "p(eval(STDIN.read))", stdin_data: program)
    out, status = Open3.capture2(model, "--json", stdin_data: program)
    lean = status.success? ? JSON.parse(out) : {}

    cases += 1
    next if cruby == "#{printed}#{expected}\n" && lean["result_repr"] == expected &&
            lean["stdout"] == printed && lean["exception"].nil?

    failures += 1
    warn "MISMATCH b=#{b} n=#{n}: theorem #{expected}, CRuby #{cruby.chomp}, model #{out.chomp}"
  end
end

puts "#{cases - failures}/#{cases} inputs: CRuby, the model and the theorem agree"
exit(failures.zero? ? 0 : 1)
