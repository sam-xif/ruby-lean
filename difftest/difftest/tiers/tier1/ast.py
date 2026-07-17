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


# ---- parameters -------------------------------------------------------------
# A `def`/block/lambda param list is a tuple whose elements are either a plain
# `str` (a required positional, back-compat) or one of these `Param` nodes. A
# `Param` is deliberately NOT a `Node`: the tier-1.5 probe walk only wraps `Node`
# leaves, so params (and any default expression they carry) are left untouched.


class Param:
    pass


@dataclass(frozen=True)
class POpt(Param):
    name: str
    default: Node  # evaluated lazily in the callee frame when the arg is omitted


@dataclass(frozen=True)
class PRest(Param):
    name: str | None  # `*a` / `*` (anonymous)


@dataclass(frozen=True)
class PKey(Param):
    name: str
    default: Node | None  # `k:` (required, None) / `k: E`


@dataclass(frozen=True)
class PKwRest(Param):
    name: str | None  # `**o` / `**` (anonymous)


@dataclass(frozen=True)
class PBlock(Param):
    name: str  # `&b`


@dataclass(frozen=True)
class PFwd(Param):
    """`...` — forwards all positional + keyword + block args to a callee."""


@dataclass(frozen=True)
class PDestr(Param):
    subparams: tuple  # (str | Param, ...) — `(a, b)` destructures one array arg


@dataclass(frozen=True)
class MethodDef(Node):
    name: str
    params: tuple  # (str | Param, ...)
    body: tuple  # statements; last is the return value


@dataclass(frozen=True)
class FwdArg(Node):
    """`...` in argument position — forwards the enclosing `def(...)`'s args."""


@dataclass(frozen=True)
class Call(Node):
    name: str
    args: tuple
    kwargs: tuple = ()  # ((keyword_name, value Node), ...)


@dataclass(frozen=True)
class IvarRead(Node):
    name: str  # includes the leading "@", e.g. "@x"


@dataclass(frozen=True)
class ClassDef(Node):
    """class Name < Super; include/prepend M; initialize; self.methods; methods; end.

    `initialize` is synthesized from `ivars`: one same-named-without-@ param per
    ivar, each stored straight into its slot (a pure ctor — no arbitrary body, so
    `.new` never triggers unbounded work; keeps generated programs terminating).
    A subclass carries `ivars == ()` and inherits its parent's `initialize`.
    """

    name: str
    superclass: str | None  # a prior class name, or None (< Object)
    mixins: tuple  # ((module_name, "include" | "prepend"), ...)
    ivars: tuple  # (str, ...) each with leading "@"; () for a subclass
    self_methods: tuple  # (MethodDef, ...) rendered as `def self.<name>`
    methods: tuple  # (MethodDef, ...) instance methods (excludes initialize)
    decls: tuple = ()  # metaprogramming class-body decls (AttrDecl/DefineMethod/...)


@dataclass(frozen=True)
class ModuleDef(Node):
    name: str
    methods: tuple  # (MethodDef, ...) instance methods, mixed in via include/prepend


@dataclass(frozen=True)
class ConstRead(Node):
    name: str  # a class/module constant, e.g. "C0"


@dataclass(frozen=True)
class Super(Node):
    args: tuple | None  # None → bare `super` (zsuper, forwards args); else `super(args)`


@dataclass(frozen=True)
class New(Node):
    class_name: str
    args: tuple


@dataclass(frozen=True)
class MethodCall(Node):
    recv: Node
    name: str
    args: tuple
    kwargs: tuple = ()  # ((keyword_name, value Node), ...)


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


# ---- item 1: blocks / procs / lambdas ---------------------------------------


@dataclass(frozen=True)
class RangeLit(Node):
    low: Node
    high: Node
    exclusive: bool


@dataclass(frozen=True)
class Yield(Node):
    args: tuple


@dataclass(frozen=True)
class BlockGiven(Node):
    pass


@dataclass(frozen=True)
class Lambda(Node):
    kind: str  # "->" | "proc" | "lambda"
    params: tuple  # (str, ...)
    body: tuple  # statements; last is the value


@dataclass(frozen=True)
class ProcCall(Node):
    recv: Node
    args: tuple


@dataclass(frozen=True)
class Block(Node):
    """A literal block attached to a `BlockCall` (never stands alone)."""

    params: tuple  # (str, ...)
    body: tuple  # statements; last is the value


@dataclass(frozen=True)
class BlockPass(Node):
    """`&expr` at a call site — expr is a proc local or a `:sym` (→ `&:sym`)."""

    expr: Node


@dataclass(frozen=True)
class BlockCall(Node):
    """recv.method(args) with a trailing block (a `Block` or a `BlockPass`).

    `recv is None` renders a bare self-send (e.g. calling a method that yields).
    """

    recv: Node | None
    method: str
    args: tuple
    block: Node  # Block | BlockPass


@dataclass(frozen=True)
class Next(Node):
    expr: Node | None


@dataclass(frozen=True)
class Break(Node):
    expr: Node | None


@dataclass(frozen=True)
class Return(Node):
    expr: Node | None


# ---- item 3: metaprogramming (heap mutation) --------------------------------


@dataclass(frozen=True)
class SendCall(Node):
    recv: Node
    method_name: str  # dispatched dynamically via `send`/`public_send`
    args: tuple
    public: bool


@dataclass(frozen=True)
class RespondTo(Node):
    recv: Node
    name: str


@dataclass(frozen=True)
class IvarGetCall(Node):
    recv: Node
    ivar: str  # with leading "@"


@dataclass(frozen=True)
class IvarSetCall(Node):
    recv: Node
    ivar: str  # with leading "@"
    value: Node


@dataclass(frozen=True)
class AttrDecl(Node):
    kind: str  # "accessor" | "reader" | "writer"
    names: tuple  # (str, ...) ivar base names (no @)


@dataclass(frozen=True)
class DefineMethod(Node):
    name: str
    params: tuple  # block params
    body: tuple
    singleton: bool  # True → define_singleton_method (a class method)


# ---- item 4: writer-calls + multiple assignment -----------------------------


@dataclass(frozen=True)
class IndexAssign(Node):
    recv: Node
    index: Node
    value: Node


@dataclass(frozen=True)
class IndexOpAssign(Node):
    recv: Node
    index: Node
    op: str  # "||=" (safe regardless of the current element)
    value: Node


@dataclass(frozen=True)
class AttrAssign(Node):
    recv: Node
    name: str  # a writer defined via attr_accessor/attr_writer
    value: Node


@dataclass(frozen=True)
class MultiAssign(Node):
    targets: tuple  # (str, ...) local names
    splat_index: int | None  # index of the `*rest` target, or None
    values: tuple  # (Node, ...) RHS expressions


@dataclass(frozen=True)
class Program(Node):
    stmts: tuple
