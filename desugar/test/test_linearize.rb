# frozen_string_literal: true

require_relative "test_helper"

# `Linearize.run`: a jump that always happens, sitting where Ruby expects a value,
# is moved out, and the operands after it (which never run) are dropped. Prism
# refuses such programs as source, so the trees are built by hand, the way the
# desugarer's own rewrites can produce them.
class TestLinearize < Minitest::Test
  BREAK = [:break, nil].freeze
  RETURN = [:return, [:int, 9]].freeze
  C = [:var, :local, "c"].freeze

  def assert_linearizes(expected, tree)
    assert_equal expected, Linearize.run(tree)
    assert_equal expected, Linearize.run(expected), "linearizing twice changes nothing"
  end

  def test_a_jump_among_arguments_ends_the_call
    assert_linearizes [:seq, [:int, 1], BREAK], [:send, nil, "f", [[:int, 1], BREAK, [:int, 2]], nil]
  end

  def test_the_receiver_runs_before_a_jumping_block_argument
    assert_linearizes [:seq, [:int, 0], RETURN], [:send, [:int, 0], "f", [], [:blockpass, RETURN]]
  end

  def test_a_jump_among_array_elements
    assert_linearizes [:seq, [:int, 1], RETURN], [:array, [[:int, 1], RETURN, [:int, 3]]]
  end

  def test_a_jumping_assigned_value
    assert_linearizes BREAK, [:vasgn, :local, "x", BREAK]
  end

  def test_a_jump_among_super_arguments
    assert_linearizes [:seq, [:int, 1], RETURN], [:super, [[:int, 1], RETURN], nil]
  end

  def test_an_if_that_jumps_on_both_branches
    assert_linearizes [:if, C, BREAK, [:next, nil]], [:send, nil, "f", [[:if, C, BREAK, [:next, nil]]], nil]
  end

  def test_an_if_that_may_fall_through_stays
    tree = [:send, nil, "f", [[:if, C, BREAK, nil]], nil]
    assert_linearizes tree, tree
  end

  def test_a_sequence_that_ends_in_a_jump
    assert_linearizes [:seq, [:int, 1], BREAK], [:send, nil, "f", [[:seq, [:int, 1], BREAK]], nil]
  end

  def test_a_tree_without_jumps_is_unchanged
    tree = [:zsuper, [:blockpass, C]]
    assert_linearizes tree, tree
  end

  def test_definitely_jumps
    assert Linearize.definitely_jumps?([:retry])
    assert Linearize.definitely_jumps?([:if, BREAK, [:int, 1], nil]), "the condition jumps"
    refute Linearize.definitely_jumps?([:if, C, BREAK, nil])
    refute Linearize.definitely_jumps?([:int, 1])
  end
end
