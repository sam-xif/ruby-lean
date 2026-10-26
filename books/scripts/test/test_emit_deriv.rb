# frozen_string_literal: true

require_relative "test_helper"

# The emitter's parts: the type join it shares with the checker (`joinT`), the
# builtin signature table, and its answer on small programs. The checker
# re-derives everything the emitter proposes, so these tests are about the
# emitter proposing what the checker will accept, not about soundness.
class TestEmitDeriv < Minitest::Test
  include EmitterTestHelper

  def test_join
    assert_equal INT, join(NEVER, INT)
    assert_equal INT, join(INT, NEVER)
    assert_equal INT, join(INT, INT)
    assert_equal nilable(INT), join(NIL_T, INT)
    assert_equal nilable(INT), join(INT, NIL_T)
    assert_equal nilable(INT), join(nilable(INT), INT)
    assert_equal nilable(INT), join(INT, nilable(INT))
    assert_equal({ "tag" => "union", "l" => INT, "r" => STR }, join(INT, STR))
    assert_equal join(INT, STR), join(join(INT, STR), STR), "a union holds each member once"
  end

  def test_spine
    assert_equal IVAR0, spine([])
    assert_equal({ "tag" => "ivarCons", "name" => "@a", "ty" => INT, "rest" => IVAR0 }, spine([["@a", INT]]))
  end

  # [receiver, method, arguments] => result type (nil: no builtin row)
  BUILTINS = [
    [INT, "+", [INT], INT], [INT, "<", [INT], BOOL], [INT, "to_s", [], STR], [INT, "even?", [], BOOL],
    [INT, "succ", [], INT], [INT, "+", [STR], nil],
    [STR, "+", [STR], STR], [STR, "upcase", [], STR], [STR, "length", [], INT], [STR, "split", [STR], array_of(STR)],
    [STR, "match?", [cls("Regexp")], BOOL], [STR, "start_with?", [STR], BOOL],
    [array_of(INT), "[]", [INT], nilable(INT)], [array_of(INT), "<<", [INT], array_of(INT)],
    [array_of(nilable(INT)), "compact", [], array_of(INT)], [array_of(INT), "uniq", [], array_of(INT)],
    [hash_of(SYM, INT), "fetch", [SYM], INT], [hash_of(SYM, INT), "fetch", [SYM, INT], INT],
    [hash_of(SYM, INT), "[]", [SYM], nilable(INT)], [hash_of(SYM, INT), "key?", [SYM], BOOL],
    [SYM, "to_s", [], STR], [BOOL, "!", [], BOOL], [FLOAT, "==", [INT], BOOL], [array_of(INT), "nil?", [], BOOL],
    [FLOAT, "+", [FLOAT], nil], [array_of(INT), "==", [INT], nil]
  ].freeze

  BUILTINS.each_with_index do |(recv, m, args, ret), i|
    define_method(:"test_builtin_#{i}_#{recv["tag"]}_#{m.gsub(/\W/) { |c| format("%02x", c.ord) }}") do
      ret.nil? ? assert_nil(prim_ret(recv, m, args)) : assert_equal(ret, prim_ret(recv, m, args))
    end
  end

  # program => the type of its value, or the reason the emitter blocks
  PROGRAMS = {
    "A = 1\nA + 1" => INT,
    "Integer" => { "tag" => "clsOf", "name" => "Integer" },
    "x = 0\nwhile x < 3\n  x += 1\nend\nx" => INT,
    "\"a\".upcase.length" => INT,
    "{ a: 1 }[:a]" => nilable(INT),
    "x = [1, nil].first\nif x.is_a?(Integer) then x + 1 else 0 end" => INT,
    "x = true ? 1 : \"a\"\nx" => { "tag" => "union", "l" => INT, "r" => STR },
    "f = ->(a) { a }\n1" => INT,
    "A = 1\nB = 2" => "a second constant",
    "f = ->(a = 1) { a }\n1" => "only required positional closure parameters are in the callable fragment",
    "[1].select { |x| x }" => "a block argument is outside the fragment",
    "[1].each { |a, b| a }" => "each requires one positional block parameter and no arguments",
    "1.5 + 2.5" => "no builtin signature for float#+/1",
    "1.foo" => "no builtin signature for int#foo/0",
    "->(a) { a }" => "closure-valued program results are outside the fragment",
    "def f = yield" => "no signature for Object#f",
    "begin; 1; rescue; 2; end" => "no rule for AST node 'begin'"
  }.freeze

  PROGRAMS.each_with_index do |(src, expected), i|
    define_method(:"test_program_#{i}") do
      result = emit_src(src)
      if expected.is_a?(String)
        assert_equal({ "status" => "blocked", "why" => expected }, result)
      else
        assert_equal "ok", result["status"], result["why"]
        assert_equal expected, result["ty"]
      end
    end
  end

  def test_a_program_too_deep_to_walk_blocks
    deep = ["int", 1]
    100_000.times { deep = ["array", [deep]] }
    assert_equal({ "status" => "blocked", "why" => "AST too deep" }, emit({ "ast" => deep }, { "sigs" => [] }))
  end

  def test_the_command_line_reads_files_or_stdin
    Dir.mktmpdir do |dir|
      ast = File.join(dir, "p.ast.json")
      sigs = File.join(dir, "p.sigs.json")
      File.write(ast, Export.json(Desugar.program("1 + 2").first))
      File.write(sigs, JSON.generate({ "sigs" => [], "dropped" => [] }))
      out, = capture_io { main(["--ast", ast, "--sigs", sigs]) }
      assert_equal "ok", JSON.parse(out)["status"]

      stdin = StringIO.new(JSON.generate({ "ast" => JSON.parse(File.read(ast))["ast"] }))
      out, = with_stdin(stdin) { capture_io { main([]) } }
      assert_equal({ "tag" => "int" }, JSON.parse(out)["ty"])
    end
  end

  def with_stdin(io)
    old = $stdin
    $stdin = io
    yield
  ensure
    $stdin = old
  end
end
