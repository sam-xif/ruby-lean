"""An `IO`/`File`/`Dir` instance has no class-side filesystem builtins.

The boot heap installs the filesystem *class* methods on the constants'
eigenclasses (`File.read`, `Dir.exist?`, …), and it used to install the same
names on the instance side too, with the same `bid`. A send to an instance
therefore answered the class-side, path-taking semantics:

    File.allocate.read("/tmp/readme.txt")   # => "hello\\n"    (CRuby: TypeError)
    File.allocate.write("/tmp/readme.txt", "zz")  # => 2, and it rewrote the fixture

`File.allocate` is how ordinary Ruby reaches such an instance, and issue #7
step 2's `File.open` descriptors are instances of the same class. Answering
where CRuby raises is the direction the repository forbids, and `read`/`size`
land in `TypeError`/`ArgumentError` — the exception family `validateD` exists to
exclude — so those were wrong answers, not gates.

Now the instance side carries no builtins of its own and every unmodeled
selector is classified by the generated CRuby name table:

* a name CRuby defines on `IO`/`File`/`Dir` (`read`, `write`, `size`, `gets`,
  …) declines with a named reason, naming the class the method really belongs
  to;
* a name CRuby defines only on the class (`exist?`, `file?`, `directory?`,
  `mkdir`) is the ordinary byte-exact `NoMethodError`;
* `respond_to?` draws the same line from the same table;
* the class side still answers over the boot fixture.

`make difftest-test` builds the model before running this suite.
"""

import pytest
from difftest.observation import Observation
from difftest.sut import LeanSUT, Unsupported

SUT = LeanSUT()

# The class side keeps answering over the boot fixture.
CLASS_SIDE = [
    ('File.read("/tmp/readme.txt")', '"hello\\n"'),
    ('File.size("/tmp/readme.txt")', "6"),
    ('File.exist?("/tmp/readme.txt")', "true"),
    ('File.file?("/tmp/readme.txt")', "true"),
    ('File.directory?("/tmp")', "true"),
]

# An instance send of a real `IO`/`File`/`Dir` instance method the model does
# not model declines, and names the class the method belongs to.
INSTANCE_GATES = [
    ('File.allocate.read("/tmp/readme.txt")', "IO#read"),
    ('IO.allocate.read("/tmp/readme.txt")', "IO#read"),
    ('File.allocate.write("/tmp/readme.txt", "zz")', "IO#write"),
    ('IO.allocate.write("/tmp/readme.txt", "zz")', "IO#write"),
    ("File.allocate.size", "File#size"),
    ("File.allocate.closed?", "IO#closed?"),
    ("File.allocate.flush", "IO#flush"),
    ("File.allocate.gets", "IO#gets"),
    ("File.allocate.each_line", "IO#each_line"),
    ("Dir.allocate.each", "Dir#each"),
    # `Dir` includes `Enumerable`, so these reach the instance through `#each`.
    ("Dir.allocate.entries", "Dir#entries"),
    ("Dir.allocate.count", "Dir#count"),
]

# A name that is a class method only is not an instance method in CRuby either,
# so the ordinary `NoMethodError` is the right answer, not a gate.
NOT_INSTANCE_METHODS = [
    (
        'File.allocate.exist?("/tmp/readme.txt")',
        "undefined method 'exist?' for an instance of File",
    ),
    ('File.allocate.file?("/tmp/readme.txt")', "undefined method 'file?' for an instance of File"),
    (
        'File.allocate.directory?("/tmp")',
        "undefined method 'directory?' for an instance of File",
    ),
    ('Dir.allocate.mkdir("/tmp/x")', "undefined method 'mkdir' for an instance of Dir"),
]

# `respond_to?` reads the same table: real instance methods answer, class-only
# names do not. (CRuby 4.0.5 agrees on every row.)
RESPONDS = [
    ("File.allocate.respond_to?(:read)", "true"),
    ("File.allocate.respond_to?(:write)", "true"),
    ("File.allocate.respond_to?(:size)", "true"),
    ("File.allocate.respond_to?(:exist?)", "false"),
    ("File.allocate.respond_to?(:file?)", "false"),
    ("File.allocate.respond_to?(:directory?)", "false"),
    ("Dir.allocate.respond_to?(:mkdir)", "false"),
    ("Dir.allocate.respond_to?(:entries)", "true"),
]


@pytest.mark.parametrize(("program", "result"), CLASS_SIDE)
def test_the_class_side_still_answers_over_the_fixture(program, result):
    """Removing the instance rows must not cost `File.*` its class methods."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result


@pytest.mark.parametrize(("program", "owner"), INSTANCE_GATES)
def test_an_instance_send_declines_by_name_instead_of_answering(program, owner):
    """The instance surface is a gate, and it names the method that is missing."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Unsupported), obs
    assert "unmodeled method " + owner in obs.reason


@pytest.mark.parametrize(("program", "message"), NOT_INSTANCE_METHODS)
def test_a_class_only_name_is_the_ordinary_no_method_error(program, message):
    """`exist?` is `File`'s singleton, so an instance has no such method."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception == ("NoMethodError", message)


@pytest.mark.parametrize(("program", "result"), RESPONDS)
def test_respond_to_follows_the_instance_table(program, result):
    """`respond_to?` answers for the instance surface, not for the class's."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result
