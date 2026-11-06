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

  def test_observe_runs_each_program_in_a_fresh_working_directory
    here = Dir.pwd
    first = Observe.run("Dir.pwd").value
    second = Observe.run("Dir.pwd").value
    refute_equal here.inspect, first
    refute_equal first, second
  end

  def test_observe_isolates_files_written_by_the_program
    assert_equal '"x"', Observe.run('File.write("probe", "x"); File.read("probe")').value
    assert_equal "false", Observe.run('File.exist?("probe")').value
    refute File.exist?(File.expand_path("probe", Dir.pwd))
  end

  def test_observe_survives_a_program_that_replaces_load_path
    assert_equal "[]", Observe.run("$LOAD_PATH.replace([]); $LOAD_PATH").value
  end

  def test_observe_reports_a_program_that_exits_before_the_observation
    obs = Observe.run("exit!")
    assert_equal "no-observation", obs.error
    assert_nil obs.exc
  end

  def test_observe_reports_why_the_observation_is_missing
    obs = Observe.run('STDERR.puts "boom"; exit! 1')
    assert_equal "no-observation", obs.error
    assert_equal ["<child-stderr>", "boom\n"], obs.exc
  end
end
