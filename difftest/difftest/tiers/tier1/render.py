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
        case _:
            return [pad + expr(node)]


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
        case _:
            raise ValueError(f"cannot render as expression: {node!r}")


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
