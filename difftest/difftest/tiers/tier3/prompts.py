"""Tier-3 prompt templates: one per semantic corner, drawn from the domains of
../ruby-lean/RubyCore/README.md artifacts 00–04 (dispatch, blocks/jumps, eval order, exceptions,
namespaces, kwargs separation, metaprogramming-as-heap-mutation)."""

from __future__ import annotations

CATEGORIES: dict[str, str] = {
    "dispatch": (
        "Method dispatch and the ancestor chain: singleton methods, `super` (with and "
        "without parens/args), modules via include/prepend changing lookup order, "
        "`method_missing` and `respond_to_missing?`, redefining methods at runtime, "
        "dispatch on subclasses vs the eigenclass."
    ),
    "blocks-jumps": (
        "Blocks, procs, lambdas and non-local jumps: proc-vs-lambda `return` semantics, "
        "`break`/`next` from blocks, `yield` with too few/many args, closures capturing "
        "and mutating locals, blocks passed with `&`, `LocalJumpError` cases."
    ),
    "eval-order": (
        "Evaluation order and once-only obligations: argument evaluation order, "
        "receiver-before-args, `a[i] += e` evaluating `a` and `i` exactly once, "
        "`||=`/`&&=` short-circuit (RHS must not evaluate when skipped), multiple "
        "assignment RHS-then-LHS order, interpolation order in strings. Use print "
        "statements inside subexpressions to make the order observable."
    ),
    "exceptions": (
        "Exceptions and unwinding: `ensure` running on all exit paths (return, break, "
        "raise), `retry`, rescue clause matching order, re-raise, exceptions raised "
        "inside `ensure`, `else` on begin blocks, custom exception classes."
    ),
    "namespaces": (
        "The five variable namespaces and constants: locals vs methods with the same "
        "name, instance/class/global variables, constant lookup through lexical nesting "
        "vs ancestors, dynamic constant assignment errors, `defined?` on each kind."
    ),
    "kwargs": (
        "Keyword vs positional-hash argument separation (Ruby 3 semantics): methods "
        "with keyword params receiving hashes and vice versa, `**` splats, optional "
        "params with defaults referencing earlier params, ArgumentError arities."
    ),
    "metaprogramming": (
        "Metaprogramming as heap mutation: `define_method`, `attr_accessor`, "
        "`instance_variable_set/get`, `send`/`public_send`, reopening classes, "
        "`Class.new`/`Module.new` with blocks, `instance_eval`/`class_eval` effects "
        "on self and definee."
    ),
}


def build_prompt(category: str, n: int) -> str:
    corner = CATEGORIES[category]
    return f"""\
You are generating adversarial test programs for a differential-testing harness that \
compares CRuby against an executable formal semantics of Ruby. Programs where the two \
disagree reveal modeling bugs, so aim for semantic corners a naive model would get wrong.

Target corner: {corner}

Generate exactly {n} distinct Ruby programs. Hard requirements for every program:
- Self-contained: no gems, no require, no file/network/environment access, no ARGV.
- Deterministic: no Time, no rand, no object_id/inspect of bare objects in output, \
no hash-ordering dependence, no threads or GC observation.
- Terminating: no unbounded loops or recursion; keep runtime well under a second.
- Observable: print evidence with `puts`/`print` so a behavioral difference shows up \
in stdout; the final expression's value is also observed.
- A program that deterministically raises is valid and useful (the exception class and \
message are observed), but most programs should run to completion.
- Keep each program under ~30 lines. Plain Ruby 3.x, parseable by `ruby -c`.

Make the {n} programs probe genuinely different aspects of the corner, including at \
least one adversarial interaction with another language feature (e.g. the corner \
inside a block, during an ensure, or interleaved with dispatch).

For each program, also provide a one-sentence description of exactly which semantic \
obligation it probes."""


# JSON schema for structured output: {"programs": [{"code", "description"}, ...]}
OUTPUT_SCHEMA = {
    "type": "object",
    "properties": {
        "programs": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "code": {"type": "string", "description": "The Ruby program source"},
                    "description": {
                        "type": "string",
                        "description": "One sentence: which semantic obligation this probes",
                    },
                },
                "required": ["code", "description"],
                "additionalProperties": False,
            },
        }
    },
    "required": ["programs"],
    "additionalProperties": False,
}
