"""Class-side dispatch fidelity for the classes the model guards by name.

`File`, `Dir`, `IO` and `Pathname` are ordinary constants in the boot heap, so a
send to one of them is a lookup miss. Which side of the line it falls on is
decided by the generated CRuby name tables, and both sides matter:

* a class method CRuby defines but the model does not (`File.mtime`,
  `Dir.mkdir`, `Pathname.glob`) must **decline with a named reason** — the model
  does not approximate, and it does not answer a guessed value;
* a name no Ruby defines (`File.zzz_does_not_exist`) must raise the ordinary
  `NoMethodError`, byte-identical to CRuby. Gating it instead would narrow the
  fragment for a name that can never work, and would hide the real method set
  behind a blanket `method_missing`.

`make difftest-test` builds the model before running this suite.
"""

import pytest
from difftest.observation import Observation
from difftest.sut import LeanSUT, Unsupported

SUT = LeanSUT()

# A name no CRuby class defines, and the message CRuby's own `NoMethodError`
# carries for a class receiver.
INVENTED = [
    ("File.zzz_does_not_exist", "undefined method 'zzz_does_not_exist' for class File"),
    ("Dir.zzz_does_not_exist", "undefined method 'zzz_does_not_exist' for class Dir"),
    ("Pathname.zzz_does_not_exist", "undefined method 'zzz_does_not_exist' for class Pathname"),
]

# A real CRuby class method the model does not model, and the class the model
# names in its reason (`IO.open` is where CRuby defines `File.open`).
UNMODELED = [
    ('File.mtime("/tmp")', "File.mtime"),
    ('Dir.mkdir("/tmp/zzz")', "Dir.mkdir"),
    ('Pathname.glob("/tmp/*")', "Pathname.glob"),
    ('File.open("/tmp/readme.txt", "r")', "IO.open"),
]

# The class-side methods the model does model keep answering.
MODELED = [
    ('File.basename("/a/b.txt")', '"b.txt"'),
    ('File.join("a", "b")', '"a/b"'),
    ('Pathname.new("/a/b.txt").basename.to_s', '"b.txt"'),
    ('File.exist?("/tmp/readme.txt")', "true"),
    ('Dir.exist?("/tmp")', "true"),
]


@pytest.mark.parametrize(("program", "message"), INVENTED)
def test_a_name_no_ruby_defines_is_the_ordinary_no_method_error(program, message):
    """Gating an invented name would answer for a name that cannot exist."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception == ("NoMethodError", message)


@pytest.mark.parametrize(("program", "reason"), UNMODELED)
def test_a_real_unmodeled_class_method_declines_by_name(program, reason):
    """A real class method is a gate that names itself, never a wrong answer."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Unsupported), obs
    assert reason in obs.reason


@pytest.mark.parametrize(("program", "result"), MODELED)
def test_a_modeled_class_method_still_answers(program, result):
    """Removing the blanket guard must not cost the methods that were modeled."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result
