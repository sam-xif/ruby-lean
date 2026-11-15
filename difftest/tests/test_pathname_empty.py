"""`Pathname#empty?` asks the filesystem, not the path String.

CRuby 4.0 defines it as

    FileTest.directory?(@path) ? Dir.empty?(@path) : File.empty?(@path)

so the answer is about the file the path names: an empty regular file is `true`,
a non-empty one is `false`, a path that does not exist is `false` (that is
`File.zero?`'s answer, not an error), and the empty path is `false` too. The
prelude used to answer `@path.empty?`, which inverted two of those cases and is
why issue #91 was filed.

Directory emptiness needs `Dir.empty?`, which the model does not have yet (VFS
step 3), so that shape must gate by name rather than answer. The fixture the
model boots with is the step-1 VFS tree: `/tmp/readme.txt` is `"hello\\n"` and
`/tmp/vfsdata/nums.txt` is `"1\\n2\\n3\\n"`.

`make difftest-test` builds the model before running this suite.
"""

import pytest
from difftest.observation import Observation
from difftest.sut import LeanSUT, Unsupported

SUT = LeanSUT()

# Answers, each checked against CRuby 4.0.5 over a real file tree with the same
# shapes (written file, missing path, empty path, trailing slash on a file).
ANSWERS = [
    ('Pathname.new("/tmp/readme.txt").empty?', "false"),
    # The file the fixture boots with has content; truncate it, then ask again.
    ('File.write("/tmp/readme.txt", "")\nPathname.new("/tmp/readme.txt").empty?', "true"),
    ('Pathname.new("/tmp/vfsdata/nums.txt").empty?', "false"),
    (
        'File.write("/tmp/vfsdata/nums.txt", "")\nPathname.new("/tmp/vfsdata/nums.txt").empty?',
        "true",
    ),
    # The empty path is not an empty file: CRuby answers false here, and the old
    # `@path.empty?` answered true.
    ('Pathname.new("").empty?', "false"),
    ('Pathname.new("/tmp/no-such-path").empty?', "false"),
    # A trailing slash on a regular file is not a directory and not zero-sized.
    ('Pathname.new("/tmp/readme.txt/").empty?', "false"),
]

# A directory's emptiness is `Dir.empty?`, a step-3 operation: gating keeps the
# answer honest instead of reporting the directory's own non-emptiness.
GATED = [
    'Pathname.new("/tmp").empty?',
    'Pathname.new("/tmp/vfsdata").empty?',
]

# The pure path operations `empty?` sits beside are unchanged.
UNCHANGED = [
    ('Pathname.new("/tmp/readme.txt").to_s', '"/tmp/readme.txt"'),
    ('Pathname.new("/a/b.lean").basename.to_s', '"b.lean"'),
    ('Pathname.new("").to_s', '""'),
]


@pytest.mark.parametrize(("program", "result"), ANSWERS)
def test_empty_asks_the_file(program, result):
    """The answer is the file's, so an empty file is true and "" is false."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result


@pytest.mark.parametrize("program", GATED)
def test_a_directory_gates_by_name(program):
    """`Dir.empty?` is unmodeled, so the directory shape declines by name."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Unsupported), obs
    assert "Pathname#empty?" in obs.reason
    assert "Dir.empty?" in obs.reason


@pytest.mark.parametrize(("program", "result"), UNCHANGED)
def test_the_pure_path_operations_are_unchanged(program, result):
    """Defining `empty?` must not turn the wrapper into a filesystem object."""
    obs = SUT.run(program + "\n")
    assert isinstance(obs, Observation), obs
    assert obs.exception is None
    assert obs.result_repr == result
