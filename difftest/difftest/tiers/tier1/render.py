"""Render the tier-1 surface AST to Ruby source.

Expressions are over-parenthesized so the emitted text re-parses to the same
structure regardless of precedence (same policy as the desugar harness's
render.rb, C2/C9).
"""

from __future__ import annotations

from . import ast as A

_INDENT = "  "


def render_program(prog: A.Program) -> str:
    return "\n".join(_stmts(prog.stmts, 0)) + "\n"


def _stmts(stmts: tuple, depth: int) -> list[str]:
    lines: list[str] = []
    for s in stmts:
        lines.extend(_stmt(s, depth))
    if not lines:
        lines.append(_INDENT * depth + "nil")
    return lines


def _stmt(node, depth: int) -> list[str]:
    pad = _INDENT * depth
    match node:
        case A.If(cond, then, orelse):
            lines = [pad + f"if {expr(cond)}"] + _stmts(then, depth + 1)
            if orelse is not None:
                lines += [pad + "else"] + _stmts(orelse, depth + 1)
            return lines + [pad + "end"]
        case A.WhileCounter(var, limit, body):
            return (
                [pad + f"{var} = 0", pad + f"while {var} < {limit}"]
                + _stmts(body, depth + 1)
                + [pad + f"{_INDENT}{var} += 1", pad + "end"]
            )
        case A.TimesBlock(count, var, body):
            return [pad + f"{count}.times do |{var}|"] + _stmts(body, depth + 1) + [pad + "end"]
        case A.MethodDef(name, params, body):
            header = pad + f"def {name}" + (f"({', '.join(params)})" if params else "")
            return [header] + _stmts(body, depth + 1) + [pad + "end"]
        case A.ClassDef():
            header = pad + f"class {node.name}" + (f" < {node.superclass}" if node.superclass else "")
            lines = [header]
            for mod, how in node.mixins:
                lines.append(pad + _INDENT + f"{how} {mod}")
            if node.ivars:
                params = [iv[1:] for iv in node.ivars]
                lines.append(pad + _INDENT + f"def initialize({', '.join(params)})")
                for iv in node.ivars:
                    lines.append(pad + _INDENT * 2 + f"{iv} = {iv[1:]}")
                lines.append(pad + _INDENT + "end")
            for d in node.decls:
                lines.extend(_stmt(d, depth + 1))
            for m in node.self_methods:
                lines.extend(_self_method(m, depth + 1))
            for m in node.methods:
                lines.extend(_stmt(m, depth + 1))
            return lines + [pad + "end"]
        case A.ModuleDef(name, methods):
            lines = [pad + f"module {name}"]
            for m in methods:
                lines.extend(_stmt(m, depth + 1))
            return lines + [pad + "end"]
        case A.Puts(args):
            return [pad + "puts(" + ", ".join(expr(a) for a in args) + ")"]
        case A.Raise(message):
            return [pad + f"raise({message!r})"]
        case A.BeginRescue(body, rescue_var, rescue_body):
            return (
                [pad + "begin"]
                + _stmts(body, depth + 1)
                + [pad + f"rescue => {rescue_var}"]
                + _stmts(rescue_body, depth + 1)
                + [pad + "end"]
            )
        case A.Next(e):
            return [pad + ("next " + expr(e) if e is not None else "next")]
        case A.Break(e):
            return [pad + ("break " + expr(e) if e is not None else "break")]
        case A.Return(e):
            return [pad + ("return " + expr(e) if e is not None else "return")]
        case A.BlockCall():
            # a block-carrying send in statement position; multi-line do/end
            return _block_call(node, depth)
        case A.IndexAssign(recv, index, value):
            return [pad + f"{expr(recv)}[{expr(index)}] = {expr(value)}"]
        case A.IndexOpAssign(recv, index, op, value):
            return [pad + f"{expr(recv)}[{expr(index)}] {op} {expr(value)}"]
        case A.AttrAssign(recv, name, value):
            return [pad + f"{expr(recv)}.{name} = {expr(value)}"]
        case A.MultiAssign(targets, splat_index, values):
            lhs = ", ".join(("*" + t if i == splat_index else t) for i, t in enumerate(targets))
            rhs = ", ".join(f"({expr(v)})" for v in values)
            return [pad + f"{lhs} = {rhs}"]
        case A.AttrDecl(kind, names):
            return [pad + f"attr_{kind} " + ", ".join(f":{n}" for n in names)]
        case A.DefineMethod(name, params, body, singleton):
            fn = "define_singleton_method" if singleton else "define_method"
            header = pad + f"{fn}(:{name}) do" + (f" |{', '.join(params)}|" if params else "")
            return [header] + _stmts(body, depth + 1) + [pad + "end"]
        case _:
            return [pad + expr(node)]


def _self_method(node, depth: int) -> list[str]:
    pad = _INDENT * depth
    header = pad + f"def self.{node.name}" + (
        f"({', '.join(node.params)})" if node.params else ""
    )
    return [header] + _stmts(node.body, depth + 1) + [pad + "end"]


def _block_call(node, depth: int) -> list[str]:
    pad = _INDENT * depth
    recv = "" if node.recv is None else expr(node.recv) + "."
    match node.block:
        case A.BlockPass(e):
            args = list(map(expr, node.args)) + ["&" + expr(e)]
            return [pad + f"{recv}{node.method}(" + ", ".join(args) + ")"]
        case A.Block(params, body):
            header = pad + f"{recv}{node.method}(" + ", ".join(expr(a) for a in node.args) + ") do"
            if params:
                header += f" |{', '.join(params)}|"
            return [header] + _stmts(body, depth + 1) + [pad + "end"]
        case _:
            raise ValueError(f"bad block: {node.block!r}")


def expr(node) -> str:
    match node:
        case A.IntLit(v):
            return str(v) if v >= 0 else f"({v})"
        case A.StrLit(v):
            return _ruby_str(v)
        case A.SymLit(name):
            return f":{name}"
        case A.BoolLit(v):
            return "true" if v else "false"
        case A.NilLit():
            return "nil"
        case A.LocalRead(name):
            return name
        case A.Assign(name, e):
            return f"({name} = {expr(e)})"
        case A.OpAssign(name, op, e):
            return f"({name} {op} {expr(e)})"
        case A.BinOp(op, left, right):
            return f"({expr(left)} {op} {expr(right)})"
        case A.And(left, right):
            return f"({expr(left)} && {expr(right)})"
        case A.Or(left, right):
            return f"({expr(left)} || {expr(right)})"
        case A.Not(e):
            return f"(!{expr(e)})"
        case A.StrInterp(parts):
            out = '"'
            for p in parts:
                if isinstance(p, str):
                    out += _escape_in_dquotes(p)
                else:
                    out += "#{" + expr(p) + "}"
            return out + '"'
        case A.ArrayLit(items):
            return "[" + ", ".join(expr(i) for i in items) + "]"
        case A.Index(recv, index):
            return f"{expr(recv)}[{expr(index)}]"
        case A.HashLit(pairs):
            return "{" + ", ".join(f"{expr(k)} => {expr(v)}" for k, v in pairs) + "}"
        case A.Call(name, args):
            return f"{name}(" + ", ".join(expr(a) for a in args) + ")"
        case A.RangeLit(low, high, exclusive):
            return f"({expr(low)}{'...' if exclusive else '..'}{expr(high)})"
        case A.Yield(args):
            return "yield(" + ", ".join(expr(a) for a in args) + ")"
        case A.BlockGiven():
            return "block_given?"
        case A.ProcCall(recv, args):
            return f"{expr(recv)}.call(" + ", ".join(expr(a) for a in args) + ")"
        case A.Lambda(kind, params, body):
            block = _braces_block(params, body, brace_params=(kind != "->"))
            if kind == "->":
                head = "->(" + ", ".join(params) + ")" if params else "->"
                return f"({head} {block})"
            return f"({kind} {block})"
        case A.BlockCall():
            # block-carrying send in expression position: { } binds tightly
            recv = "" if node.recv is None else expr(node.recv) + "."
            match node.block:
                case A.BlockPass(e):
                    args = list(map(expr, node.args)) + ["&" + expr(e)]
                    return f"({recv}{node.method}(" + ", ".join(args) + "))"
                case A.Block(params, body):
                    call = f"{recv}{node.method}(" + ", ".join(expr(a) for a in node.args) + ")"
                    return f"({call} {_braces_block(params, body, brace_params=True)})"
                case _:
                    raise ValueError(f"bad block: {node.block!r}")
        case A.IvarRead(name):
            return name
        case A.ConstRead(name):
            return name
        case A.SendCall(recv, method_name, args, public):
            fn = "public_send" if public else "send"
            parts = [f":{method_name}"] + [expr(a) for a in args]
            return f"{expr(recv)}.{fn}(" + ", ".join(parts) + ")"
        case A.RespondTo(recv, name):
            return f"{expr(recv)}.respond_to?(:{name})"
        case A.IvarGetCall(recv, ivar):
            return f"{expr(recv)}.instance_variable_get(:{ivar})"
        case A.IvarSetCall(recv, ivar, value):
            return f"{expr(recv)}.instance_variable_set(:{ivar}, {expr(value)})"
        case A.Super(args):
            return "super" if args is None else "super(" + ", ".join(expr(a) for a in args) + ")"
        case A.New(class_name, args):
            return f"{class_name}.new(" + ", ".join(expr(a) for a in args) + ")"
        case A.MethodCall(recv, name, args):
            return f"{expr(recv)}.{name}(" + ", ".join(expr(a) for a in args) + ")"
        case _:
            raise ValueError(f"cannot render as expression: {node!r}")


def _braces_block(params: tuple, body: tuple, brace_params: bool) -> str:
    inner = "\n".join(_stmts(body, 0))
    if brace_params and params:
        return "{ |" + ", ".join(params) + "|\n" + inner + "\n}"
    return "{\n" + inner + "\n}"


def _ruby_str(s: str) -> str:
    return '"' + _escape_in_dquotes(s) + '"'


def _escape_in_dquotes(s: str) -> str:
    out = []
    for ch in s:
        if ch in ('"', "\\", "#"):
            out.append("\\" + ch)
        elif ch == "\n":
            out.append("\\n")
        else:
            out.append(ch)
    return "".join(out)
