# frozen_string_literal: true

require_relative "test_helper"

# The JSON the model reads (`Export.json`): its version, and the encoding of
# each kind of value.
class TestExport < Minitest::Test
  include DesugarTestHelper

  def export(src) = JSON.parse(Export.json(core(src)))

  def test_the_document_carries_the_format_version
    assert_equal({ "v" => Export::VERSION, "ast" => ["int", 1] }, export("1"))
  end

  def test_symbols_become_strings_and_nil_becomes_null
    assert_equal ["vasgn", "local", "a", ["nil"]], export("a = nil")["ast"]
    assert_equal ["send", nil, "f", [], nil], export("f()")["ast"]
  end

  def test_each_numeric_literal_gets_its_own_site
    assert_equal ["send", ["rat", 1, 1, "program:0"], "+", [["rat", 2, 1, "program:1"]], nil],
                 export("1r + 2r")["ast"]
  end

  def test_the_literal_namespace_names_the_sites
    doc = JSON.parse(Export.json(core("1r"), literal_namespace: "prelude"))
    assert_equal ["rat", 1, 1, "prelude:0"], doc["ast"]
  end

  def test_an_imaginary_float_keeps_its_bits
    assert_equal ["imag", ["flt_bits", [1.5].pack("G").unpack1("Q>")], "program:0"], export("1.5i")["ast"]
    assert_equal ["imag", ["int", 2], "program:0"], export("2i")["ast"]
  end

  def test_a_regexp_literal_has_its_own_node
    assert_equal ["regexp_lit", "a", 1], export("/a/i")["ast"]
  end

  def test_an_explicit_regexp_new_with_other_arguments_stays_a_send
    assert_equal "send", export("Regexp.new(a, 0)")["ast"][0]
  end

  def test_a_float_that_is_not_finite_is_refused
    assert_raises(ArgumentError) { Export.json([:flt, Float::INFINITY]) }
  end

  def test_an_unexpected_value_is_refused
    assert_raises(ArgumentError) { Export.json([:str, :not_a_string_payload, Object.new]) }
  end
end
