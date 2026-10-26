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
  READER_GAPS = {}.freeze

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
