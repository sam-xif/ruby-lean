# frozen_string_literal: true

# Loaded first by every test file. Measures line and branch coverage of
# desugar/lib/ (`make desugar-unit` compares it with coverage-baseline.json).
require "simplecov"

SimpleCov.start do
  root File.expand_path("../..", __dir__)
  coverage_dir ".make/coverage/desugar"
  command_name "desugar-unit"
  enable_coverage :branch
  cover "desugar/lib/**/*.rb"
  formatter SimpleCov::Formatter::SimpleFormatter
end

$LOAD_PATH.unshift File.expand_path("../lib", __dir__)
require "minitest/autorun"
require "open3"
require "json"
require "prism"
require "desugar"
require "export"
require "linearize"
require "render"
require "rubycore"

module DesugarTestHelper
  def self.included(base) = base.extend(ClassMethods)

  module ClassMethods
    def test_name(label) = label.gsub(/[^a-z0-9_]+/, "_")

    # For each `label => [program, core program or nil]`: the desugarer produces
    # that core program (when given), and the result has the properties every
    # core program must have.
    def core_program_tests(examples)
      examples.each do |label, (src, expected)|
        name = test_name(label)
        define_method(:"test_#{name}_output") { assert_equal expected, core(src) } if expected
        define_method(:"test_#{name}_is_well_formed") { assert_nil RubyCore.explain(core(src)) }
        define_method(:"test_#{name}_is_linearized") do
          program = core(src)
          assert_equal program, Linearize.run(program)
        end
        define_method(:"test_#{name}_renders_to_ruby") do
          rendered = Render.core(core(src))
          assert_predicate Prism.parse(rendered), :success?, rendered
        end
        define_method(:"test_#{name}_exports") do
          assert_kind_of Hash, JSON.parse(Export.json(core(src)))
        end
      end
    end
  end

  # The core program for `src`, and the rules that fired.
  def desugar(src) = Desugar.program(src)

  def core(src) = desugar(src).first

  def assert_unsupported(src, reason)
    error = assert_raises(Desugar::Unsupported) { desugar(src) }
    assert_includes error.message, reason
  end
end
