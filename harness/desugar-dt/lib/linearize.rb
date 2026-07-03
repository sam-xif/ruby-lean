# frozen_string_literal: true

# Linearization — hoist *unconditional* control-flow jumps out of operand position so the
# RubyCore tree can be rendered to valid Ruby text.
#
# Ruby accepts a jump (next/break/return) in a STATEMENT position (a seq element, an
# if/while body, an if/ternary/case branch) — even when the enclosing `if` is itself an
# operand — but REJECTS a jump in OPERAND position (send receiver/arg, array/hash element,
# assignment RHS, if/while condition): `(next).to_s` and `foo(next)` are SyntaxErrors,
# while `(if c then next else 5 end).to_s` is fine. See docs/semantics/linearization.md.
#
# Key consequence: we only ever hoist an operand that NEVER yields a value
# (`definitely_jumps?`), so **no temporaries are needed** — we evaluate the operands up to
# and including the jumping one as statements, and drop the unreachable remainder (which is
# exactly what CRuby's compiler does with a jump + dead code).
module Linearize
  module_function

  # Does evaluating `node` always transfer control (never fall through with a value)?
  def definitely_jumps?(node)
    case node[0]
    when :return, :break, :next, :retry then true
    when :seq  then node[1..].any? { |n| definitely_jumps?(n) }
    when :if
      c, t, e = node[1], node[2], node[3]
      definitely_jumps?(c) || (definitely_jumps?(t) && !e.nil? && definitely_jumps?(e))
    else false
    end
  end

  # Rewrite so no unconditional jump sits in operand position. Identity on jump-free trees.
  def run(node)
    case node[0]
    when :int, :flt, :str, :sym, :true, :false, :nil, :self, :var, :const
      node
    when :vasgn
      v = run(node[3]); definitely_jumps?(v) ? v : [:vasgn, node[1], node[2], v]
    when :casgn
      v = run(node[2]); definitely_jumps?(v) ? v : [:casgn, node[1], v]
    when :return, :break, :next
      return node if node[1].nil?
      v = run(node[1]); definitely_jumps?(v) ? v : [node[0], v]
    when :send
      recv = node[1] ? run(node[1]) : nil
      args = node[3].map { |a| run(a) }
      blk  = node[4] ? [:block, node[4][1], run(node[4][2])] : nil
      hoist((recv ? [recv] : []) + args) || [:send, recv, node[2], args, blk]
    when :array
      elems = node[1].map { |e| run(e) }
      hoist(elems) || [:array, elems]
    when :hash
      flat = node[1].flatten(1).map { |e| run(e) }
      hoist(flat) || [:hash, flat.each_slice(2).to_a]
    when :if
      c = run(node[1])
      return c if definitely_jumps?(c)
      [:if, c, run(node[2]), node[3] && run(node[3])]
    when :while
      c = run(node[1])
      return c if definitely_jumps?(c)
      [:while, c, run(node[2])]
    when :def   then [:def, node[1], node[2], run(node[3])]
    when :defs  then [:defs, run(node[1]), node[2], node[3], run(node[4])]
    when :block then [:block, node[1], run(node[2])]
    when :seq   then [:seq, *node[1..].map { |n| run(n) }]
    when :splat then node[1] ? [:splat, run(node[1])] : node
    # Structural heads: bodies are statement positions (no hoisting needed there), but we
    # recurse so operand-position jumps *inside* them (e.g. a def in a class body) linearize.
    when :class  then [:class, node[1], node[2] && run(node[2]), run(node[3])]
    when :module then [:module, node[1], run(node[2])]
    when :sclass then [:sclass, run(node[1]), run(node[2])]
    when :begin
      _, body, rescues, els, ens = node
      rs = rescues.map { |excs, ref, h| [excs.map { |e| run(e) }, ref, run(h)] }
      [:begin, run(body), rs, els && run(els), ens && run(ens)]
    when :super
      args = node[1].map { |a| run(a) }
      blk  = node[2] ? [:block, node[2][1], run(node[2][2])] : nil
      hoist(args) || [:super, args, blk]
    when :zsuper then [:zsuper, node[1] ? [:block, node[1][1], run(node[1][2])] : nil]
    else node
    end
  end

  # If some operand (in evaluation order, already linearized) definitely jumps, return the
  # sequence of operands up to and including it (dropping the unreachable rest). Else nil.
  def hoist(ops)
    i = ops.index { |o| definitely_jumps?(o) }
    return nil if i.nil?
    kept = ops[0..i]
    kept.length == 1 ? kept[0] : [:seq, *kept]
  end
end
