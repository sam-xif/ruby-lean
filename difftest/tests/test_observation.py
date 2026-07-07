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
