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
    print(f"Body inference: {len(cases)} pipeline controls and caller independence passed")


if __name__ == "__main__":
    main()
