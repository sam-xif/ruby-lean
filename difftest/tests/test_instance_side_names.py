"""Instance-side dispatch fidelity for the filesystem classes.

`File`, `IO` and `Dir` are the model's filesystem classes: `File.allocate` gives
an instance with no descriptor builtin behind it, and a `File.open` descriptor
(issue #7 step 2) will be one too. Which side of the line an unmodeled selector
falls on is decided by the generated CRuby name tables, and both sides matter:

* an instance method CRuby defines and the model does not (`File#path`,
  `IO#fileno`, `Dir#entries`) must **decline with a named reason**. The model
  does not approximate, and it must not land in the `NoMethodError` family that
  `validateD` is meant to exclude — that is a wrong answer, not a gate;
* a name no Ruby defines (`f.zzz_does_not_exist`) must raise the ordinary
  `NoMethodError`, byte-identical to CRuby. Gating it instead would answer for a
  name that can never work;
* `respond_to?` answers from the same table, so a real selector is `true` and an
  invented one is `false`.

`make difftest-test` builds the model before running this suite.
"""

import pytest
from difftest.observation import Observation
from difftest.sut import LeanSUT, Unsupported

SUT = LeanSUT()

# A name no CRuby class defines, and the message CRuby's own `NoMethodError`
# carries for an instance receiver.
INVENTED = [
    (
        "File.allocate.zzz_does_not_exist",
        "undefined method 'zzz_does_not_exist' for an instance of File",
    ),
    (
        "IO.allocate.zzz_does_not_exist",
        "undefined method 'zzz_does_not_exist' for an instance of IO",
    ),
    (
        "Dir.allocate.zzz_does_not_exist",
        "undefined method 'zzz_does_not_exist' for an instance of Dir",
    ),
]

# An instance method CRuby defines and the model does not model, with the owner
# the model names in its reason: `File` inherits every one of these from `IO`.
UNMODELED = [
    ("File.allocate.path", "IO#path"),
    ("File.allocate.fileno", "IO#fileno"),
    ("File.allocate.eof", "IO#eof"),
    ("File.allocate.eof?", "IO#eof?"),
    ("File.allocate.binmode", "IO#binmode"),
    ("File.allocate.tty?", "IO#tty?"),
    ("File.allocate.sync", "IO#sync"),
    ("File.allocate.reopen('/tmp/readme.txt')", "IO#reopen"),
    ("IO.allocate.pos", "IO#pos"),
    ("Dir.allocate.path", "Dir#path"),
]

# `respond_to?` draws the same line, so a real selector answers and an invented
# one does not (CRuby: `true` / `false`).
RESPONDS = [
    ("File.allocate.respond_to?(:path)", "true"),
    ("File.allocate.respond_to?(:fileno)", "true"),
    ("File.allocate.respond_to?(:zzz_does_not_exist)", "false"),
]

# The instance methods the model does model keep answering.
MODELED = [
    ("File.allocate.class", "File"),
    ("File.allocate.is_a?(IO)", "true"),
]


@pytest.mark.parametrize(("program", "message"), INVENTED)
def test_a_name_no_ruby_defines_is_the_ordinary_no_method_error(program, message):
    """Gating an invented name would answer for a name that cannot exist."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception == ("NoMethodError", message)


@pytest.mark.parametrize(("program", "owner"), UNMODELED)
def test_a_real_unmodeled_instance_method_declines_by_name(program, owner):
    """A real instance method is a gate that names itself, never a wrong answer."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Unsupported), obs
    assert "unmodeled method " + owner in obs.reason


@pytest.mark.parametrize(("program", "result"), RESPONDS)
def test_respond_to_follows_the_same_table(program, result):
    """`respond_to?` answers for the real surface, not for every name."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result


@pytest.mark.parametrize(("program", "result"), MODELED)
def test_a_modeled_instance_method_still_answers(program, result):
    """The new table must not cost the instance surface the model does have."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result
