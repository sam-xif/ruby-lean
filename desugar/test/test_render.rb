# frozen_string_literal: true

require_relative "test_helper"

# `Render.core`: a core program back to Ruby source, for the round-trip test.
class TestRender < Minitest::Test
  include DesugarTestHelper

  def render(src) = Render.core(core(src))

  def test_rescue_clauses_else_and_ensure
    assert_equal "(begin; nil; rescue (A), (B) => e; 1; else; 2; ensure; 3; end)",
                 render("begin; rescue A, B => e; 1; else; 2; ensure; 3; end")
  end

  def test_every_kind_of_parameter
    assert_equal "(def f(a, b = (1), *c, d:, e: (2), **f, &g); 1; end)",
                 render("def f(a, b = 1, *c, d:, e: 2, **f, &g) = 1")
    assert_equal "(def f(*, **, &); 1; end)", render("def f(*, **, &) = 1")
    assert_equal "(def f(...); 1; end)", render("def f(...) = 1")
  end

  def test_nested_destructuring
    assert_equal "([[1]]).each() { |(a, (b, *c))| a }", render("[[1]].each { |(a, (b, *c))| a }")
  end

  def test_keyword_arguments_render_as_keywords_not_a_hash
    assert_equal "f(**(h), (:a) => (1))", render("f(**h, a: 1)")
  end

  def test_rational_literals_are_exact_decimals
    assert_equal "3.25r", render("3.25r")
    assert_equal "-0.5r", render("-0.5r")
    assert_equal "0.1r", render("0.1r")
    assert_equal "3r", render("3r")
  end

  def test_constant_paths
    assert_equal "(Foo)::Bar", render("Foo::Bar")
    assert_equal "::Foo", render("::Foo")
  end

  def test_definitions
    assert_equal "(class A < (B); nil; end)", render("class A < B; end")
    assert_equal "(def (self).f(x); x; end)", render("def self.f(x) = x")
    assert_equal "(begin; (begin; nil; end); end while ((a).!()))", render("begin; end until a")
  end

  def test_an_unknown_head_or_parameter_is_an_error
    assert_raises(RuntimeError) { Render.core([:nope]) }
    assert_raises(RuntimeError) { Render.core([:def, "f", [[:pnope]], [:nil]]) }
  end
end
