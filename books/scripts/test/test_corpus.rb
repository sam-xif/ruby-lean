# frozen_string_literal: true

require_relative "test_helper"

# The emitter on every program of the checker's corpus (books/corpus/), with
# signatures read by `read_sigs.rb`: the path the browser playground takes.
# `make soundness` runs the same programs with Sorbet's signatures and then
# the checker; this measures the emitter and the reader on their own.
class TestCorpus < Minitest::Test
  include EmitterTestHelper

  CORPUS = File.join(ROOT, "books/corpus")
  ACCEPTED = File.readlines(File.join(CORPUS, "accepted.txt"), chomp: true).freeze

  # Programs the checker accepts with Sorbet's signatures, but for which
  # `read_sigs.rb` misses a signature, and why the emitter then blocks. The list
  # may only shrink: when the reader learns one, its test fails until the entry
  # is removed.
  READER_GAPS = {
    "073-class-factory-method" => "no signature for <Class:Point>#origin",
    "077-module-basic" => "no signature for <Class:M>#foo",
    "078-module-method-with-arg" => "no signature for <Class:Greeter>#hello",
    "079-module-multiple-methods" => "no signature for <Class:M>#foo",
    "080-module-method-calls-method" => "no signature for <Class:M>#value",
    "081-module-with-arithmetic" => "no signature for <Class:Calc>#add",
    "082-module-calling-another-module" => "no signature for <Class:M2>#bar",
    "083-module-returns-array" => "no signature for <Class:M>#pair",
    "084-module-boolean-method" => "no signature for <Class:M>#positive?",
    "085-module-nested-call-chain" => "no signature for <Class:M>#greeting",
    "086-module-passing-multiple-args" => "no signature for <Class:M>#sum3",
    "095-block-param-ampersand" => "run: missing declared block signature",
    "146-const-attr-reader" => "no signature for Point#x",
    "157-param-block" => "run: missing declared block signature",
    "261-bound-block-alias-and-yield" => "run: missing declared block signature",
    "267-param-nilable-positional" => "no signature for <Class:Shelf>#tax"
  }.freeze

  Dir.glob(File.join(CORPUS, "*.rb")).sort.each do |path|
    base = File.basename(path, ".rb")
    name = base.tr("-", "_")

    if ACCEPTED.include?(base) && !READER_GAPS.key?(base)
      define_method(:"test_#{name}_has_a_derivation") do
        result = pipeline(File.read(path))
        assert_equal "ok", result["status"], result["why"]
      end
    elsif READER_GAPS.key?(base)
      define_method(:"test_#{name}_is_still_a_reader_gap") do
        assert_equal({ "status" => "blocked", "why" => READER_GAPS[base] }, pipeline(File.read(path)))
      end
    else
      # Not accepted by the checker: the emitter may propose a derivation the
      # checker rejects, or block; it must not fail.
      define_method(:"test_#{name}_gets_an_answer") do
        result = pipeline(File.read(path))
        assert(result.is_a?(Array) || %w[ok blocked].include?(result["status"]), result.inspect)
      end
    end
  end

  def test_every_reader_gap_is_an_accepted_program
    assert_equal [], READER_GAPS.keys - ACCEPTED
  end
end
