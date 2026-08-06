from difftest.observation import Observation


def test_address_normalization_is_allocation_ordered():
    a = Observation(
        stdout="#<Foo:0x0000a1b2c3d4> #<Bar:0x0000ffff0000> #<Foo:0x0000a1b2c3d4>",
        result_repr="#<Bar:0x0000ffff0000>",
        exception=None,
    ).normalized()
    assert a.stdout == "#<Foo:<addr0>> #<Bar:<addr1>> #<Foo:<addr0>>"
    assert a.result_repr == "#<Bar:<addr1>>"


def test_same_structure_different_addresses_agree():
    a = Observation("#<Foo:0x00001111aaaa>", "nil", None).normalized()
    b = Observation("#<Foo:0x00002222bbbb>", "nil", None).normalized()
    assert a == b


def test_exception_message_normalized():
    a = Observation("", None, ("NoMethodError", "undefined for #<Foo:0x000012345678>"))
    assert a.normalized().exception == ("NoMethodError", "undefined for #<Foo:<addr0>>")


def test_json_roundtrip():
    a = Observation("out", None, ("RuntimeError", "boom"), timed_out=False)
    assert Observation.from_json(a.to_json()) == a


def test_sorbet_location_lines_are_normalized_away():
    """RubyCore has no line numbers, so a model can never reproduce sorbet's
    `Caller:`/`Definition:` suffix. Normalizing it away is what lets the Sorbet
    corpus be compared against the Lean model at all."""
    from difftest.observation import Observation

    cruby = Observation(
        stdout="1\n",
        result_repr=None,
        exception=(
            "TypeError",
            "Parameter 'x': Expected type Integer, got type String with value \"two\"\n"
            "Caller: /tmp/prog.rb:19\n"
            "Definition: /tmp/prog.rb:14 (Object#stringify)",
        ),
    )
    model = Observation(
        stdout="1\n",
        result_repr=None,
        exception=(
            "TypeError",
            "Parameter 'x': Expected type Integer, got type String with value \"two\"",
        ),
    )
    assert cruby.normalized() == model.normalized()


def test_normalization_does_not_touch_stdout_or_the_message_body():
    """The rule is narrow on purpose: only exception messages, only lines with
    exactly that shape. A program printing such a line keeps it."""
    from difftest.observation import Observation

    a = Observation(stdout="Caller: mine\n", result_repr=None, exception=None)
    assert a.normalized().stdout == "Caller: mine\n"
    b = Observation(stdout="", result_repr=None, exception=("E", "boom\nCallerX: keep"))
    assert b.normalized().exception == ("E", "boom\nCallerX: keep")
