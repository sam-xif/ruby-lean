#!/usr/bin/env ruby
# frozen_string_literal: true

# The theorems are about the model. Whether the model is Ruby is a separate
# question, and this asks it of these two programs: it compares what the
# theorems predict with what CRuby and the model's own binary do, on a grid of
# inputs.
#
#   ruby books/Books/FastPower/check.rb     # needs `make run` at the repository root
#
# For each program and each (b, n) the two literals in the .rb file are
# replaced and the program is run. It must print b ** n and have the value
# b ** n (`ComputesPower`), and the model must take the number of transitions
# the theorems give (`Slow.cost`, `Fast.cost`).
require "json"
require "open3"
require "rbconfig"

here = __dir__
model = File.join(here, "../../../bin/ruby-lean")

# `Fast.loopCost`, as in Fast/Proof.lean.
def fast_loop_cost(left)
  return 18 if left.zero?

  (left.odd? ? 43 : 36) + fast_loop_cost(left / 2)
end

# Transitions before the one that finishes the program; the model's own count
# includes that last one.
costs = {
  "slow_power.rb" => ->(n) { 24 * n + 65 },
  "fast_power.rb" => ->(n) { 51 + fast_loop_cost(n) }
}

failures = 0
cases = 0
costs.each do |file, cost|
  source = File.read(File.join(here, file))
  [-7, -1, 0, 1, 2, 3, 10, 12_345_678_901_234_567_890].each do |b|
    [0, 1, 2, 3, 5, 6, 13, 64, 100, 255].each do |n|
      program = source.sub("Power.new(3)", "Power.new(#{b})").sub("raise_to(13)", "raise_to(#{n})")
      raise "literals not found in #{file}" if program == source && [b, n] != [3, 13]

      power = b**n
      cruby, = Open3.capture2(RbConfig.ruby, "-e", "p(eval(STDIN.read))", stdin_data: program)
      out, status = Open3.capture2(model, "--json", stdin_data: program)
      lean = status.success? ? JSON.parse(out) : {}
      steps_out, steps_status = Open3.capture2(model, "--steps", stdin_data: program)
      steps = steps_status.success? ? JSON.parse(steps_out)["steps"] : nil

      cases += 1
      next if cruby == "#{power}\n#{power}\n" && lean["result_repr"] == power.to_s &&
              lean["stdout"] == "#{power}\n" && lean["exception"].nil? && steps == cost.(n) + 1

      failures += 1
      warn "MISMATCH #{file} b=#{b} n=#{n}: theorem #{power} in #{cost.(n) + 1} steps, " \
           "CRuby #{cruby.inspect}, model #{out.chomp} in #{steps.inspect} steps"
    end
  end
end

puts "#{cases - failures}/#{cases} runs: CRuby, the model and the theorems agree"
exit(failures.zero? ? 0 : 1)
