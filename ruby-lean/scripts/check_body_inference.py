#!/usr/bin/env python3
"""Exercise missing-signature proposals through Sorbet, emission and validateD."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from build_corpus import EXPORT, ROOT, strip


def run_json(command, data=None):
    return json.loads(subprocess.check_output(command, input=data, text=True))


def source(body, call='"reader"', sig=""):
    return f'''# typed: true
module Welcome
  extend T::Sig
  {sig}
  def self.render(input)
    {body}
  end
end
{f"Welcome.render({call})" if call is not None else ""}
'''


def main():
    cases = [
        ("alias", source('saved = input; "greetings " + saved'), "ok", True),
        ("wrong_domain", source('saved = input; "greetings " + saved', "7"), "ok", False),
        ("uncalled_conflict", source('1 + input; "hello " + input', None), "blocked", False),
        ("explicit_untyped", source('"hello " + input', sig=
            "sig { params(input: T.untyped).returns(T.untyped) }"), "blocked", False),
        ("partial_annotation", source('"hello " + input', sig=
            "sig { params(input: Integer) }"), "blocked", False),
        ("callee_constraint", '''# typed: true
module Welcome
  def self.format(input)
    "hello " + input
  end
  def self.relay(value)
    Welcome.format(value)
  end
end
Welcome.relay("reader")
''', "ok", True),
        ("implicit_spellings", '''# typed: true
module Welcome
  def self.x; 21; end
  def self.describe; x + x(); end
end
Welcome.describe
''', "ok", True),
        ("implicit_arguments", '''# typed: true
module Welcome
  def self.increment(input); input + 1; end
  def self.relay(value); increment(value); end
end
Welcome.relay(7)
''', "ok", True),
        ("saved_lambda_receiver", '''# typed: true
f = ->(x) { x + 1 }
f.call(f = 2)
''', "ok", True),
        ("earlier_lambda_argument", '''# typed: true
->(x, y) { x + 1 }.call(a = 2, a = nil)
''', "ok", True),
        ("lambda_parameter_shadow", '''# typed: true
x = nil
->(x) { x + 1 }.call(2)
x
''', "ok", True),
        ("lambda_parameter_type_leak", '''# typed: true
x = nil
->(x) { x + 1 }.call(2)
x + 1
''', "blocked", False),
        ("lambda_block_local_shadow", '''# typed: true
x = 7
->(y; x) { x = nil; y + 1 }.call(2)
x + 1
''', "ok", True),
        ("lambda_live_capture", '''# typed: true
x = 1
f = ->(y) { x + y }
x = 2
f.call(3)
''', "ok", True),
        ("lambda_unsafe_capture", '''# typed: true
x = 1
f = ->(y) { x + y }
x = nil
f.call(3)
''', "blocked", False),
        ("proc_array_argument", '''# typed: true
proc { |x| x[0] }.call([7])
''', "ok", True),
        ("proc_two_arguments", '''# typed: true
proc { |x, y| x + y }[2, 3]
''', "ok", True),
        ("proc_missing_argument", '''# typed: true
proc { |x, y| x }.call(1)
''', "blocked", False),
        ("proc_extra_argument", '''# typed: true
proc { |x| x }.call(1, 2)
''', "blocked", False),
        ("proc_unsafe_argument", '''# typed: true
proc { |x| x * 2 }.call(nil)
''', "blocked", False),
        ("proc_next_escape", '''# typed: true
proc { |x| next x }.call(1)
''', "blocked", False),
        ("each_body_result", '''# typed: true
[1, 2, 3].each { |item| item.to_s }
''', "ok", True),
        ("each_empty", '''# typed: true
[].each { |item| 7 }
''', "ok", True),
        ("each_capture_write", '''# typed: true
total = 0
[1, 2, 3].each { |item| total = total + item }
total
''', "ok", True),
        ("each_capture_type_change", '''# typed: true
total = 0
[1].each { |item| total = nil }
''', "blocked", False),
        ("each_parameter_shadow", '''# typed: true
item = nil
[1].each { |item| item + 1 }
item
''', "ok", True),
        ("each_parameter_type_leak", '''# typed: true
item = nil
[1].each { |item| item + 1 }
item + 1
''', "blocked", False),
        ("each_block_local_shadow", '''# typed: true
saved = 7
[1].each { |item; saved| saved = nil; item + 1 }
saved + 1
''', "ok", True),
        ("each_receiver_assignment", '''# typed: true
(items = [1, 2]).each { |item| item + 1 }
''', "ok", True),
        ("each_unsafe_element", '''# typed: true
[nil].each { |item| item + 1 }
''', "blocked", False),
        ("each_extra_argument", '''# typed: true
[1].each(2) { |item| item + 1 }
''', "blocked", False),
        ("each_extra_parameter", '''# typed: true
[1].each { |item, extra| item + 1 }
''', "blocked", False),
        ("each_next_escape", '''# typed: true
[1].each { |item| next item }
''', "blocked", False),
        ("map_string_results", '''# typed: true
strings = [1, 2].map { |item| item.to_s }
strings.map { |word| word.length }
''', "ok", True),
        ("collect_integer_results", '''# typed: true
[1, 2].collect { |item| item + 1 }
''', "ok", True),
        ("map_empty", '''# typed: true
[].map { |item| "result" }
''', "ok", True),
        ("map_capture_write", '''# typed: true
total = 0
[1, 2].map { |item| total = total + item }
total + 1
''', "ok", True),
        ("map_capture_type_change", '''# typed: true
total = 0
[1].map { |item| total = nil }
''', "blocked", False),
        ("map_body_local", '''# typed: true
[1, 2].map do |item|
  doubled = item * 2
  doubled + 1
end
''', "ok", True),
        ("map_block_local_shadow", '''# typed: true
saved = 4
[1].map { |item; saved| saved = nil; item.to_s }
saved + 1
''', "ok", True),
        ("map_parameter_type_leak", '''# typed: true
item = nil
[1].map { |item| item + 1 }
item + 1
''', "blocked", False),
        ("map_unsafe_element", '''# typed: true
[nil].map { |item| item + 1 }
''', "blocked", False),
        ("map_extra_argument", '''# typed: true
[1].map(2) { |item| item + 1 }
''', "blocked", False),
        ("map_extra_parameter", '''# typed: true
[1].map { |item, extra| item + 1 }
''', "blocked", False),
        ("map_next_escape", '''# typed: true
[1].map { |item| next item }
''', "blocked", False),
    ]
    emitted = {}
    with tempfile.TemporaryDirectory(prefix="ruby-body-inference-") as directory:
        for name, ruby, status, expected in cases:
            path = Path(directory) / f"{name}.rb"
            path.write_text(ruby)
            sigs = run_json([sys.executable, str(Path(ROOT) / "scripts/srb_sigs.py"), "--quiet", str(path)])
            ast = run_json([EXPORT], strip(ruby))
            proposal = run_json(["ruby", str(Path(ROOT) / "scripts/emit_deriv.rb")],
                                json.dumps({"ast": ast, "sigs": sigs}))
            assert proposal["status"] == status, (name, proposal)
            accepted = False
            if status == "ok":
                emitted[name] = proposal["deriv"]
                verdict = run_json([str(Path(ROOT) / ".lake/build/bin/validate-one")],
                                   json.dumps({"program": ast, "deriv": proposal["deriv"]}))
                accepted = verdict["validateD"]
            assert accepted == expected, (name, accepted, expected)
    # Changing the caller's value/type cannot change the method's proposed domain.
    assert emitted["alias"]["stmts"][0] == emitted["wrong_domain"]["stmts"][0]
    print(f"Body inference and block flow: {len(cases)} pipeline controls and caller independence passed")


if __name__ == "__main__":
    main()
