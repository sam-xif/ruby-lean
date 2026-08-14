"""Tier-1 generation heads for the Homebrew slice's feature set (`PLAN.md` W4b).

The existing tier-1 grammar generates control flow, dispatch and the object
model; it generates **nothing** the version + vulnerability slice actually leans
on. This module adds those heads: regex literals with the `String`/`Regexp`/
`MatchData` surface, `<=>` chains with `Comparable`, `T::Struct`, and
abstract/override hierarchies.

Two design decisions, because they are what make these heads *useful* rather
than merely present:

1. **Probes, not grammar sprinkles.** Weaving a regex literal into `_expr` as one
   more depth-limited head would generate patterns against random strings, where
   almost every match fails and every program tests the same "no match" arm.
   Instead each family emits a self-contained statement block over a **matched
   pair** — a pattern drawn together with subjects it was written for — and prints
   every intermediate. High information per program; the comparison stays per
   line, so a single wrong answer still localizes.
2. **The pattern pool is bounded by the engine's feature set** (W4b: "so the
   generator and engine grow together"), and by D2 for backreferences: `matchBR`
   may legitimately gate, so backref patterns are a small deliberate share.
   A gate is safe but buys nothing, and swamping the head with them would cost
   most of the head.

Every observation here is value-level and process-independent by construction —
no address, no `hash`, no `Float`. N38 is what happens when that slips.
"""

from __future__ import annotations

from hypothesis import strategies as st

from . import ast as A


def _show(node: A.Node) -> A.Node:
    """`puts(x.inspect)` — `.inspect` so `nil` is distinguishable from `""`."""
    return A.Puts((A.MethodCall(node, "inspect", ()),))


def _rescued(body: tuple, var: str = "ex") -> A.Node:
    """Run `body`, and on a raise print `Class: message` instead of ending the
    program — so one expected ArgumentError does not hide every later line."""
    report = A.Puts(
        (
            A.StrInterp(
                (
                    "",
                    A.MethodCall(A.LocalRead(var), "class", ()),
                    ": ",
                    A.MethodCall(A.LocalRead(var), "message", ()),
                )
            ),
        )
    )
    return A.BeginRescue(body, var, (report,))


# ─── Regex + the String / Regexp / MatchData surface ────────────────────────

# Patterns inside the engine's fragment (W2a `Syntax.lean`): literals, classes,
# `.`, concat, alt, star/plus/opt, bounded `{n,m}`, groups (capturing,
# non-capturing, named), anchors, lookahead. The shapes are the slice's own —
# dotted numerics, prerelease suffixes, URL fragments — because those are the
# populations `Version`/`Semver`/`Purl`/`Identify` actually feed the matcher.
RX_POOL: tuple[tuple[str, str], ...] = (
    (r"\d+", ""),
    (r"\d+\.\d+", ""),
    (r"(\d+)\.(\d+)\.(\d+)", ""),
    (r"^(\d+)\.(\d+)(?:\.(\d+))?$", ""),
    (r"(?<major>\d+)\.(?<minor>\d+)", ""),
    (r"[a-z]+", ""),
    (r"[A-Za-z]+[-_]?\d*", ""),
    (r"[^0-9]+", ""),
    (r"a*", ""),
    (r"a+b?", ""),
    (r"\d{1,3}", ""),
    (r"\d{2}", ""),
    (r"(rc|beta|alpha)\d*", ""),
    (r"(?:v)?(\d[\d.]*)", ""),
    (r"\A\d+\z", ""),
    (r"\d+$", ""),
    (r"(?=\d)\w+", ""),
    (r"(?!x)\w+", ""),
    (r"x|y|zap", ""),
    (r"\.", ""),
    (r"[-._]", ""),
    (r"ok", "i"),
    (r"OK", "i"),
    (r"\s+", ""),
    (r"", ""),  # the empty pattern — matches at 0, exercises the zero-width advance
)

# D2: `matchBR` may gate rather than answer, so these stay rare.
RX_BACKREF_POOL: tuple[tuple[str, str], ...] = ((r"(\d)\1", ""), (r"(a|b)-\1", ""))

# Subjects chosen so the pool above both matches and misses on real content.
RX_SUBJECT_POOL: tuple[str, ...] = (
    "1.2.3", "1.2", "10.20.30", "0.1.0-rc.1", "v2.4", "1.2.3_1",
    "abc", "ok", "OK", "zap-42", "es5-shim-4.6.7", "a b", "", "11", "aab", "x.y",
)

# No backreference syntax (`\1`) in a replacement — the model gates a replacement
# containing a backslash on purpose, so it would only cost coverage.
RX_REPL_POOL: tuple[str, ...] = ("-", "", "Z", "<>")

TR_POOL: tuple[tuple[str, str], ...] = (
    ("a-z", "A-Z"), ("0-9", "#"), ("abc", "x"), ("^0-9", "."), ("aeiou", ""),
)


@st.composite
def regex_probe(draw, idx: int) -> tuple:
    """A self-contained regex / String-pattern probe block.

    Every MatchData read is guarded by `(md && …)` rather than rescued: a miss is
    then an observable `nil` instead of a NoMethodError that ends the program and
    hides every line after it.
    """
    src, flags = draw(
        st.one_of(
            st.sampled_from(RX_POOL),
            st.sampled_from(RX_POOL),
            st.sampled_from(RX_POOL),
            st.sampled_from(RX_BACKREF_POOL),
        )
    )
    subject = draw(st.sampled_from(RX_SUBJECT_POOL))
    rep = draw(st.sampled_from(RX_REPL_POOL))
    tr_from, tr_to = draw(st.sampled_from(TR_POOL))
    limit = draw(st.sampled_from([None, -1, 2]))
    blk_meth = draw(st.sampled_from(["sub", "gsub"]))

    rxv, sjv, mv = f"rx{idx}", f"sj{idx}", f"md{idx}"
    rx, sj, md = A.LocalRead(rxv), A.LocalRead(sjv), A.LocalRead(mv)
    guarded = lambda name, args=(): A.And(md, A.MethodCall(md, name, args))  # noqa: E731

    split_args: tuple = (rx,) if limit is None else (rx, A.IntLit(limit))
    stmts: list[A.Node] = [
        A.Assign(rxv, A.RegexLit(src, flags)),
        A.Assign(sjv, A.StrLit(subject)),
        _show(A.MethodCall(rx, "source", ())),
        _show(A.MethodCall(rx, "to_s", ())),
        _show(A.BinOp("=~", sj, rx)),
        _show(A.MethodCall(sj, "match?", (rx,))),
        _show(A.MethodCall(rx, "match?", (sj,))),
        A.Assign(mv, A.MethodCall(rx, "match", (sj,))),
        _show(A.MethodCall(md, "nil?", ())),
        _show(md),
        _show(A.And(md, A.Index(md, A.IntLit(0)))),
        _show(guarded("captures")),
        _show(guarded("to_a")),
        _show(guarded("pre_match")),
        _show(guarded("post_match")),
        _show(guarded("names")),
        _show(guarded("named_captures")),
        _show(guarded("size")),
        _show(A.MethodCall(sj, "scan", (rx,))),
        _show(A.MethodCall(sj, "sub", (rx, A.StrLit(rep)))),
        _show(A.MethodCall(sj, "gsub", (rx, A.StrLit(rep)))),
        _show(A.MethodCall(sj, "split", split_args)),
        _show(A.MethodCall(sj, "tr", (A.StrLit(tr_from), A.StrLit(tr_to)))),
        # the block form — the path a builtin cannot serve (L110), and the one
        # `Purl.encode` actually takes
        _show(
            A.BlockCall(
                sj, blk_meth, (rx,), A.Block(("w",), (A.MethodCall(A.LocalRead("w"), "upcase", ()),))
            )
        ),
        # `$~` and friends are *views* of the last match, not stored globals (L101)
        _show(A.GvarRead("$~")),
        _show(A.GvarRead("$1")),
        _show(A.GvarRead("$&")),
    ]
    return tuple(stmts)


# ─── Interpolated regex literals (W4c obligations 2 and 3) ──────────────────

# Pattern fragments that are valid on their own, so `/pre#{piece}post/` parses.
RX_PIECE_POOL: tuple[str, ...] = ("a", r"\d", "[ab]", "x|y", r"\d+")
RX_INTERP_SHELL: tuple[tuple[str, str], ...] = (("", ""), ("x", ""), ("", "y"), (r"\A", ""))


@st.composite
def regex_interp_probe(draw, idx: int) -> tuple:
    """An interpolated regex literal, reached repeatedly inside a loop.

    This is `PLAN.md` W4c's remaining pair of obligations, as a *generator* head
    rather than the one-off seeds C33 got: the interpolation is evaluated **every
    time** the literal is reached, and `/o` evaluates it **once** for the life of
    the program. Neither is visible from a single evaluation, which is why the
    literal sits in a loop — and under tier 1.5 the interpolated operand is
    probe-wrapped, so the trace *counts* the evaluations instead of merely
    agreeing on the final value.
    """
    piece = draw(st.sampled_from(RX_PIECE_POOL))
    pre, post = draw(st.sampled_from(RX_INTERP_SHELL))
    subject = draw(st.sampled_from(RX_SUBJECT_POOL))
    flags = draw(st.sampled_from(["", "", "o"]))
    pv, lv = f"ip{idx}", f"ik{idx}"
    lit = A.RegexInterp((pre, A.LocalRead(pv), post), flags)
    body = (
        _show(A.BinOp("=~", A.StrLit(subject), lit)),
        _show(A.MethodCall(lit, "source", ())),
    )
    return (
        A.Assign(pv, A.StrLit(piece)),
        A.WhileCounter(lv, draw(st.integers(2, 3)), body),
    )


# ─── `<=>` chains and `Comparable` ──────────────────────────────────────────


@st.composite
def comparable_probe(draw, idx: int) -> tuple:
    """A `Comparable` class over one ivar, then the whole mixin surface.

    Its `<=>` answers `nil` for a non-sibling argument, which is what makes
    `<`/`>` raise `ArgumentError: comparison of Cmp0 with 1 failed`. That is
    generated on purpose: the message is what L111 got wrong by gating where CRuby
    answers, and `vulnerability.rb:202` (`Version.new(a) <=> Version.new(b) ||
    raise(Uncomparable)`) is exactly this shape.
    """
    cname = f"Cmp{idx}"
    keys = draw(st.lists(st.integers(-3, 9), min_size=2, max_size=4))
    cmp_body = (
        A.If(
            A.MethodCall(A.LocalRead("o"), "is_a?", (A.ConstRead(cname),)),
            (A.BinOp("<=>", A.IvarRead("@v"), A.MethodCall(A.LocalRead("o"), "v", ())),),
            (A.NilLit(),),
        ),
    )
    cls = A.ClassDef(
        name=cname,
        superclass=None,
        mixins=(("Comparable", "include"),),
        ivars=("@v",),
        self_methods=(),
        methods=(A.MethodDef("<=>", ("o",), cmp_body),),
        decls=(A.AttrDecl("reader", ("v",)),),
    )
    names = [f"c{idx}_{i}" for i in range(len(keys))]
    stmts: list[A.Node] = [cls]
    stmts += [A.Assign(n, A.New(cname, (A.IntLit(k),))) for n, k in zip(names, keys)]

    a, b, last = A.LocalRead(names[0]), A.LocalRead(names[1]), A.LocalRead(names[-1])
    for op in ("<=>", "==", "<", "<=", ">", ">="):
        stmts.append(_show(A.BinOp(op, a, b)))
    stmts.append(_show(A.MethodCall(a, "between?", (b, last))))
    stmts.append(_show(A.MethodCall(A.MethodCall(a, "clamp", (b, last)), "v", ())))

    # sort / min / max / sort_by, each mapped back to the key so the observation is
    # the *ordering* and not an object address
    arr = A.ArrayLit(tuple(A.LocalRead(n) for n in names))
    key_of = lambda recv: A.BlockCall(  # noqa: E731
        recv, "map", (), A.Block(("e",), (A.MethodCall(A.LocalRead("e"), "v", ()),))
    )
    stmts.append(_show(key_of(A.MethodCall(arr, "sort", ()))))
    stmts.append(
        _show(
            key_of(
                A.BlockCall(
                    arr, "sort_by", (), A.Block(("e",), (A.MethodCall(A.LocalRead("e"), "v", ()),))
                )
            )
        )
    )
    stmts.append(_show(A.MethodCall(A.MethodCall(arr, "min", ()), "v", ())))
    stmts.append(_show(A.MethodCall(A.MethodCall(arr, "max", ()), "v", ())))

    # the ArgumentError arm — `<=>` returns nil, so Comparable raises
    for op in ("<", ">=", "<="):
        stmts.append(_rescued((_show(A.BinOp(op, a, A.IntLit(1))),)))
    # ...but `==` answers false rather than raising [V]
    stmts.append(_show(A.BinOp("==", a, A.IntLit(1))))
    stmts.append(_show(A.BinOp("<=>", a, A.IntLit(1))))
    return tuple(stmts)
