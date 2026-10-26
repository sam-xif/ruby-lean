# frozen_string_literal: true

require_relative "test_helper"

# `read_sigs.rb`: signatures read off the annotated source with Prism.
class TestReadSigs < Minitest::Test
  # Sorbet's printed type => the `Ty` it reads as (nil: no claim made).
  TYPES = {
    "Integer" => { "tag" => "int" },
    "String" => { "tag" => "cls", "name" => "String" },
    "T::Boolean" => { "tag" => "bool" },
    "NilClass" => { "tag" => "nilT" },
    "Symbol" => { "tag" => "sym" },
    "Float" => { "tag" => "float" },
    "Foo" => { "tag" => "cls", "name" => "Foo" },
    "T.noreturn" => { "tag" => "never" },
    "void" => { "tag" => "any" },
    "T.nilable(Integer)" => { "tag" => "nilable", "elem" => { "tag" => "int" } },
    "T.nilable(NilClass)" => { "tag" => "nilT" },
    "T.class_of(Foo)" => { "tag" => "clsOf", "name" => "Foo" },
    "T::Array[Integer]" => { "tag" => "arrayOf", "elem" => { "tag" => "int" } },
    "T::Hash[Symbol, Integer]" => { "tag" => "hashOf", "key" => { "tag" => "sym" }, "val" => { "tag" => "int" } },
    "T.any(Integer, String)" => { "tag" => "union", "l" => { "tag" => "int" },
                                  "r" => { "tag" => "cls", "name" => "String" } },
    "T.any(NilClass, Integer)" => { "tag" => "nilable", "elem" => { "tag" => "int" } },
    "T.any(Integer, NilClass)" => { "tag" => "nilable", "elem" => { "tag" => "int" } },
    "T.any(NilClass, NilClass)" => { "tag" => "nilT" },
    "T.any(Integer, Integer)" => { "tag" => "int" },
    "T.untyped" => nil,
    "T.proc.void" => nil,
    "A::B" => nil,
    "T.class_of(A::B)" => nil,
    "T::Hash[Integer]" => nil,
    "T::Array[T.untyped]" => nil,
    "T.nilable(T.untyped)" => nil,
    "T.any(Integer, String, Symbol)" => nil,
    "" => nil
  }.freeze

  TYPES.each_with_index do |(sorbet, ty), i|
    define_method(:"test_type_#{i}_#{sorbet.gsub(/\W+/, "_")}") do
      ty.nil? ? assert_nil(to_ty(sorbet)) : assert_equal(ty, to_ty(sorbet))
    end
  end

  def test_untyped_reads_as_any_when_asked
    assert_equal({ "tag" => "any" }, to_ty("T.untyped", "any"))
  end

  def test_split_args_respects_brackets
    assert_equal ["A", "T::Hash[B, C]", "D"], split_args("A, T::Hash[B, C], D")
  end

  def test_a_signature
    sigs, errors = read_sigs(<<~RUBY)
      extend T::Sig
      class Point
        sig { params(x: Integer, y: T.nilable(String)).returns(T::Boolean) }
        def ok?(x, y) = true
      end
    RUBY
    assert_empty errors
    assert_equal [{ "cls" => "Point", "name" => "ok?", "line" => 4,
                    "params" => [{ "name" => "x", "ty" => { "tag" => "int" } },
                                 { "name" => "y",
                                   "ty" => { "tag" => "nilable", "elem" => { "tag" => "cls", "name" => "String" } } }],
                    "ret" => { "tag" => "bool" } }], sigs["sigs"]
    assert_equal "not-checked", sigs["verdict"], "the reader never claims Sorbet's approval"
  end

  # Each method the reader does not file, and why.
  DROPPED = {
    "module M\n  sig { returns(Integer) }\n  def self.a = 1\nend" => "module owner M -- outside the fragment",
    "class A::B\n  sig { returns(Integer) }\n  def b = 1\nend" =>
      "namespaced owner A::B -- Ty.cls carries flat names here",
    "sig { params(x: T.untyped).returns(Integer) }\ndef c(x) = 1" => "parameter x not in Ty: T.untyped",
    "sig { returns(T.proc.void) }\ndef d = 1" => "return type not in Ty: T.proc.void",
    "def e = 1" => "no declared return type",
    "sig { params(x: Integer).returns(Integer) }\ndef g(x, y) = 1" => "no declared type for parameter y"
  }.freeze

  DROPPED.each_with_index do |(src, why), i|
    define_method(:"test_drops_#{i}_#{why.split.first(3).join("_").gsub(/\W+/, "_")}") do
      sigs, = read_sigs(src)
      assert_empty sigs["sigs"]
      assert_equal([why], sigs["dropped"].map { |d| d["why"] })
    end
  end

  def test_a_parse_error_reads_no_signatures
    sigs, errors = read_sigs("def f(")
    refute_empty errors
    assert_equal "parse-error", sigs["verdict"]
    assert_empty sigs["sigs"]
  end
end
