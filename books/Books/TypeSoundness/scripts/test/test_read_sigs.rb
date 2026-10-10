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
    "module A\n  class B\n    sig { returns(Integer) }\n    def b = 1\n  end\nend" =>
      "namespaced owner A::B -- Ty.cls carries flat names here",
    "class P\n  class << self\n    sig { returns(Integer) }\n    def self.a = 1\n  end\nend" =>
      "unsupported singleton owner <Class:<Class:P>>",
    "o = Object.new\nsig { returns(Integer) }\ndef o.a = 1" => "singleton method on o -- outside the fragment",
    "class P\n  attr_reader :c\nend" => "no declared return type",
    "sig { params(b: T.proc.returns(Integer)).returns(Integer) }\ndef r(&b) = 1" =>
      "block parameter b not supported: T.proc.returns(Integer)",
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

  # Each method as Sorbet's symbol table files it: owner, name, parameters, and
  # the declared block. Checked against `srb_sigs.py` on the same source.
  FILED = {
    "module M\n  sig { returns(Integer) }\n  def a = 1\nend" =>
      [["M", "a", [], { "tag" => "int" }]],
    "module M\n  sig { returns(Integer) }\n  def self.a = 1\nend" =>
      [["<Class:M>", "a", [], { "tag" => "int" }]],
    "class P\n  class << self\n    sig { returns(Integer) }\n    def a = 1\n  end\nend" =>
      [["<Class:P>", "a", [], { "tag" => "int" }]],
    "class P\n  sig { returns(Integer) }\n  attr_reader :x, :y\nend" =>
      [["P", "x", [], { "tag" => "int" }], ["P", "y", [], { "tag" => "int" }]],
    "class P\n  sig { params(b: Integer).returns(Integer) }\n  attr_writer :b\nend" =>
      [["P", "b=", [{ "name" => "b", "ty" => { "tag" => "int" } }], { "tag" => "int" }]],
    "class P\n  sig { returns(Integer) }\n  attr_accessor :a\nend" =>
      [["P", "a", [], { "tag" => "int" }],
       ["P", "a=", [{ "name" => "a", "ty" => { "tag" => "int" } }], { "tag" => "int" }]]
  }.freeze

  FILED.each_with_index do |(src, want), i|
    define_method(:"test_files_#{i}_#{want.first[0..1].join("_").gsub(/\W+/, "_")}") do
      sigs, = read_sigs(src)
      assert_empty sigs["dropped"]
      assert_equal(want, sigs["sigs"].map { |s| [s["cls"], s["name"], s["params"], s["ret"]] })
    end
  end

  def test_a_declared_block
    sigs, = read_sigs(<<~RUBY)
      sig { params(n: Integer, b: T.proc.params(x: Integer, y: Symbol).returns(Integer)).returns(Integer) }
      def run(n, &b) = b.call(n, :k)
    RUBY
    assert_equal [{ "cls" => "Object", "name" => "run", "line" => 2,
                    "params" => [{ "name" => "n", "ty" => { "tag" => "int" } }], "ret" => { "tag" => "int" },
                    "block" => { "name" => "b", "args" => [{ "tag" => "int" }, { "tag" => "sym" }],
                                 "ret" => { "tag" => "int" } } }], sigs["sigs"]
  end

  def test_an_anonymous_block_has_no_block_signature
    sigs, = read_sigs("sig { returns(Integer) }\ndef run(&) = 1")
    refute sigs["sigs"].first.key?("block")
  end

  def test_a_block_type_outside_ty_is_not_a_signature
    assert_nil block_signature("T.proc.params(x: T.untyped).returns(Integer)")
    assert_nil block_signature("T.proc.params(x).returns(Integer)")
    assert_nil block_signature("T.proc.params(x: Integer).returns(T.untyped)")
    assert_nil block_signature(nil)
  end

  def test_a_parse_error_reads_no_signatures
    sigs, errors = read_sigs("def f(")
    refute_empty errors
    assert_equal "parse-error", sigs["verdict"]
    assert_empty sigs["sigs"]
  end
end
