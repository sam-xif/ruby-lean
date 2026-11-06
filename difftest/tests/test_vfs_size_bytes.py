"""The VFS reports byte counts, not character counts.

`File.size` and the value `File.write` returns are byte counts in CRuby. The
model stores file contents as Lean strings, whose `String.length` is a character
count, so a UTF-8 file used to be one byte per character. This is a wrong
answer, not a gate: the program printed a different number under the two
implementations.
"""

from pathlib import Path

import pytest
from difftest.compare import Verdict
from difftest.control import CRubyRunner
from difftest.runner import run_case
from difftest.sut import LeanSUT
from difftest.testcase import TestCase as Case

# The model's boot fixture has this file (`RubyCore/Heap.lean` §Virtual
# filesystem), so both sides may write to it. CRuby uses the host's copy, which
# the fixture restores afterwards.
HOST_FILE = Path("/tmp/readme.txt")

PROGRAM = """\
p File.write("/tmp/readme.txt", "é\\n")
p File.size("/tmp/readme.txt")
p File.write("/tmp/readme.txt", "世界")
p File.size("/tmp/readme.txt")
"""


@pytest.fixture
def restore_host_file():
    original = HOST_FILE.read_bytes() if HOST_FILE.exists() else None
    try:
        yield
    finally:
        if original is None:
            HOST_FILE.unlink(missing_ok=True)
        else:
            HOST_FILE.write_bytes(original)


def test_file_size_and_write_count_bytes(restore_host_file):
    result = run_case(
        Case(id="vfs-size-bytes", source=PROGRAM, tier=3),
        CRubyRunner(),
        LeanSUT(),
    )
    assert result.verdict is Verdict.AGREE, result.reason
    assert result.sut_obs.stdout == "3\n3\n6\n6\n"
