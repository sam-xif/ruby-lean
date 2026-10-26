# frozen_string_literal: true

require_relative "test_helper"

# `RubyCore.explain`, the structural check every desugared program passes
# before it is rendered or exported: what it rejects, and the reason it gives.
class TestRubyCore < Minitest::Test
  # [malformed node, the reason]
  MALFORMED = [
    [5, "not an array: 5"],
    [[:nope], "unknown head :nope"],
    [[:int, 1.0], "int payload not Integer"],
    [[:flt, 1], "flt payload not Float"],
    [[:rat, 1, 0], "invalid rational literal"],
    [[:imag, [:str, "a"]], "invalid imaginary literal"],
    [[:str, 1], ":str payload not String"],
    [%i[sym a], ":sym payload not String"],
    [[:var, :weird, "a"], "var kind invalid: :weird"],
    [[:var, :local, 1], "var name not String"],
    [[:vasgn, :local, "a", 5], "not an array: 5"],
    [[:const, 1], "const name not String"],
    [[:send, nil, :f, [], nil], "send mname not String"],
    [[:send, nil, "f", [[:nope]], nil], "send arg: unknown head :nope"],
    [[:block, [[:bad, "x"]], [], [], [:nil]], "block params: unknown param head :bad"],
    [[:block, [[:popt, "x", [:nope]]], [], [], [:nil]], "block params: popt default: unknown head :nope"],
    [[:def, 1, [], [:nil]], "def name not String"],
    [[:def, "f", [[:pfwd, 1]], [:nil]], "def params: :pfwd takes no fields"],
    [[:def, "f", [[:pdestr, [[:preq, 1]]]], [:nil]], "def params: pdestr subs: preq name not String"],
    [[:def, "f", [[:pkey, "a", [:nope]]], [:nil]], "def params: popt/pkey default: unknown head :nope"],
    [[:def, "f", [[:prest, 1]], [:nil]], "def params: prest name not String/nil"],
    [[:def, "f", "x", [:nil]], "def params: params not Array"],
    [[:def, "f", [5], [:nil]], "def params: param not array: 5"],
    [[:array, 5], "array payload not Array"],
    [[:hash, [[1]]], "hash pair not [k,v]"],
    [[:if, [:nope], [:nil], nil], "if child: unknown head :nope"],
    [[:break, 1], "not an array: 1"],
    [[:class, 1, nil, [:nil]], "class name: name must be String or cpath"],
    [[:class, [:cpath, nil, 1], nil, [:nil]], "class name: cpath name not String"],
    [[:begin, [:nil], [[[[:nope]], nil, [:nil]]], nil, nil], "rescue exc: unknown head :nope"],
    [[:begin, [:nil], [[[], [:local, 1], [:nil]]], nil, nil], "rescue ref not [kind, name]"],
    [[:begin, [:nil], [[[], [:weird, "e"], [:nil]]], nil, nil], "rescue ref kind invalid: :weird"],
    [[:begin, [:nil], 5, nil, nil], "begin rescues not Array"],
    [[:for, [[:weird, "x"]], [:nil], [:nil]], "for target kind invalid: :weird"],
    [[:for, [[:local, "x"]], [:nope], [:nil]], "for coll: unknown head :nope"],
    [[:dowhile, [:nope], [:nil]], "dowhile body: unknown head :nope"],
    [[:fwd, 1], ":fwd takes no children"],
    [[:kwargs, 5], "kwargs payload not Array"],
    [[:kwargs, [5]], "kwargs elem not Array"],
    [[:kwargs, [[:kwsplat, [:nope]]]], "kwsplat expr: unknown head :nope"],
    [[:kwargs, [[[:nil]]]], "kwargs assoc not [k,v]"],
    [[:kwargs, [[[:nope], [:nil]]]], "kwargs key: unknown head :nope"],
    [[:kwargs, [[[:nil], [:nope]]]], "kwargs val: unknown head :nope"],
    [[:yield, [[:nope]]], "yield arg: unknown head :nope"],
    [[:undef, [1]], "undef names not Array of String"],
    [[:alias, 1, "b"], "alias names not String"],
    [[:seq, [:nope]], "seq child: unknown head :nope"],
    [[:super, [[:nope]], nil], "super arg: unknown head :nope"],
    [[:sclass, [:nope], [:nil]], "sclass obj: unknown head :nope"],
    [[:defs, [:nope], "f", [], [:nil]], "defs recv: unknown head :nope"],
    [[:redo, 1], ":redo takes no children"],
    [[:retry, 1], ":retry takes no children"],
    [[:self, 1], ":self takes no children"]
  ].freeze

  MALFORMED.each_with_index do |(node, reason), i|
    define_method(:"test_rejects_malformed_node_#{i}_#{node.inspect[0, 24].gsub(/\W+/, "_")}") do
      assert_equal reason, RubyCore.explain(node)
      refute RubyCore.is_core?(node)
    end
  end

  def test_every_head_in_the_list_is_one_the_check_knows
    RubyCore::HEADS.each_key do |head|
      refute_equal "unknown head :#{head}", RubyCore.explain([head])
    end
  end
end
