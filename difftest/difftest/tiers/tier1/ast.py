"""Surface-Ruby AST for the tier-1 generator.

Deliberately independent of the desugar harness's RubyCore: this is a *surface*
vocabulary (with sugar like &&/||, op-assign, interpolation) whose programs are
rendered to text and fed to any SUT. Loops appear only in bounded counter form
so generated programs terminate by construction (prong2-design §4).
"""

from __future__ import annotations

from dataclasses import dataclass


class Node:
    pass


@dataclass(frozen=True)
class IntLit(Node):
    value: int


@dataclass(frozen=True)
class StrLit(Node):
    value: str


@dataclass(frozen=True)
class SymLit(Node):
    name: str


@dataclass(frozen=True)
class BoolLit(Node):
    value: bool


@dataclass(frozen=True)
class NilLit(Node):
    pass


@dataclass(frozen=True)
class LocalRead(Node):
    name: str


@dataclass(frozen=True)
class Assign(Node):
    name: str
    expr: Node


@dataclass(frozen=True)
class OpAssign(Node):
    name: str
    op: str  # "+=", "-=", "*=", "||="
    expr: Node


@dataclass(frozen=True)
class BinOp(Node):
    op: str  # + - * == < > <= >= %
    left: Node
    right: Node


@dataclass(frozen=True)
class And(Node):
    left: Node
    right: Node


@dataclass(frozen=True)
class Or(Node):
    left: Node
    right: Node


@dataclass(frozen=True)
class Not(Node):
    expr: Node


@dataclass(frozen=True)
class StrInterp(Node):
    parts: tuple  # str | Node


@dataclass(frozen=True)
class ArrayLit(Node):
    items: tuple


@dataclass(frozen=True)
class Index(Node):
    recv: Node
    index: Node


@dataclass(frozen=True)
class HashLit(Node):
    pairs: tuple  # ((key Node, value Node), ...)


@dataclass(frozen=True)
class If(Node):
    cond: Node
    then: tuple  # statements
    orelse: tuple | None


@dataclass(frozen=True)
class WhileCounter(Node):
    """var = 0; while var < limit; body; var += 1; end  — terminates by construction."""

    var: str
    limit: int
    body: tuple


@dataclass(frozen=True)
class TimesBlock(Node):
    count: int
    var: str
    body: tuple


@dataclass(frozen=True)
class MethodDef(Node):
    name: str
    params: tuple  # (str, ...)
    body: tuple  # statements; last is the return value


@dataclass(frozen=True)
class Call(Node):
    name: str
    args: tuple


@dataclass(frozen=True)
class Puts(Node):
    args: tuple


@dataclass(frozen=True)
class Raise(Node):
    message: str


@dataclass(frozen=True)
class BeginRescue(Node):
    body: tuple
    rescue_var: str
    rescue_body: tuple


@dataclass(frozen=True)
class Program(Node):
    stmts: tuple
