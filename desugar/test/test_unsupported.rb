# frozen_string_literal: true

require_relative "test_helper"

# Programs the desugarer must decline, and the reason it gives. Declining is
# how the front end stays faithful: a construct it cannot translate exactly is
# reported, never approximated.
class TestUnsupported < Minitest::Test
  include DesugarTestHelper

  EXAMPLES = {
    "a parse error" => ["1 +", "parse error"],
    "__LINE__" => ["__LINE__", "__LINE__/__FILE__"],
    "__FILE__" => ["__FILE__", "__LINE__/__FILE__"],
    "a backtick string" => ["`ls`", "backtick x-string"],
    "a flip-flop" => ["if (a==1)..(a==2) then 1 end", "flip-flop operator"],
    "an unknown node type" => ["BEGIN { 1 }", "node type :pre_execution_node"],
    "pattern matching" => ["1 => a", "node type :match_required_node"],
    "eval of a string" => ['eval("1")', "eval of string"],
    "instance_eval of a string" => ['instance_eval("1")', "instance_eval of string"],
    "a for loop with a rest target" => ["for a, *b in c; end", "for multi-target with rest"],
    "**nil" => ["def f(*a, **nil) = 1", "keyword-rest :no_keywords_parameter_node"],
    "a top-level return" => ["return 1", "top-level return"],
    "a splat in return" => ["def f = return *a", "splat in return"],
    "an attribute target" => ["a.b, c = 1, 2", "massign target :call_target_node"],
    "an index target" => ["a[0], c = 1, 2", "massign target :index_target_node"],
    "a regex encoding flag" => ["/a/u", "regex encoding flag"],
    "a safe-navigation op-assign" => ["a&.b += 1", "safe-navigation op-assign"],
    "a hash splat" => ["{ **a }", "hash element :assoc_splat_node"],
    "an `it` block parameter" => ["[1].each { it }", "block param type :it_parameters_node"]
  }.freeze

  EXAMPLES.each do |label, (src, reason)|
    define_method(:"test_declines_#{test_name(label)}") { assert_unsupported(src, reason) }
  end

  def test_the_command_line_exits_3_with_the_reason
    exe = File.expand_path("../bin/export-json", __dir__)
    out, err, status = Open3.capture3(RbConfig.ruby, exe, stdin_data: "`ls`")
    assert_equal 3, status.exitstatus
    assert_empty out
    assert_includes err, "backtick x-string"
  end
end
