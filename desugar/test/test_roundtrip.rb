# frozen_string_literal: true

require_relative "test_helper"
require "roundtrip"

# The round-trip check (`Roundtrip.check`) and the observation it rests on
# (`Observe.run`), which runs a program under CRuby. Each test here starts a
# CRuby process.
class TestRoundtrip < Minitest::Test
  # Prints "x" each time `x` is evaluated, and `x` is falsy.
  ORDER = "def x; print \"x\"; nil; end; x && 1"

  def test_a_faithful_translation_agrees
    result = Roundtrip.check(ORDER)
    assert_equal :agree, result.status
    assert result.normal_form
    assert result.ast_idempotent
  end

  def test_evaluating_an_operand_twice_is_caught_by_the_output
    result = Roundtrip.check(ORDER, inject_bug: true)
    assert_equal :disagree, result.status
    assert_equal :trace, result.bucket
    assert_equal 'stdout: "x" vs "xx"', result.reason
  end

  def test_a_declined_program_is_reported_with_the_reason
    result = Roundtrip.check("`ls`")
    assert_equal :out_of_fragment, result.status
    assert_includes result.reason, "backtick x-string"
  end

  def test_an_exception_is_part_of_the_observation
    result = Roundtrip.check('raise ArgumentError, "m"')
    assert_equal :agree, result.status
    assert_equal %w[ArgumentError m], result.obs_src.exc
  end

  def test_the_triage_of_a_disagreement
    a = Observe::Obs.new(stdout: "a", value: "1")
    assert_equal :value_exc, Roundtrip.bucket_for(a, Observe::Obs.new(stdout: "a", value: "2"))
    assert_equal :trace, Roundtrip.bucket_for(a, Observe::Obs.new(stdout: "b", value: "1"))
    assert_equal 'value: "1" vs "2" | exc: nil vs ["E", "m"]',
                 Roundtrip.diff(a, Observe::Obs.new(stdout: "a", value: "2", exc: %w[E m]))
  end

  def test_observe_captures_output_and_value
    assert_equal({ stdout: "1\n", value: ":sym", exc: nil, error: nil }, Observe.run("puts 1; :sym").to_h)
  end

  def test_observe_hides_object_addresses
    assert_equal "#<Object:0xXXXX>\n", Observe.run("p Object.new").stdout
  end

  def test_observe_survives_a_value_that_cannot_be_inspected
    assert_equal "<uninspectable>", Observe.run("x = Object.new; def x.inspect = raise; x").value
  end

  def test_observe_stops_a_program_that_runs_too_long
    assert_equal "timeout", Observe.run("sleep 5", timeout: 1).error
  end
end
