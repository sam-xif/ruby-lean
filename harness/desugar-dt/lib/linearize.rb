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
  # Reconstruct a send/super block slot with its operands linearized. A literal block's
  # body is a *deferred* position (called later, not an operand), so we only recurse into it;
  # params/locals are binding positions. A block-pass `&e` holds an *operand* (evaluated at
  # the call, last) — we linearize `e` here, and the caller also feeds it to `hoist` so an
  # unconditional jump inside `&e` aborts the call correctly.
  def blk_of(b)
    return nil if b.nil?
    case b[0]
    when :block     then [:block, run_params(b[1]), b[2], run(b[3])]
    when :blockpass then [:blockpass, b[1] && run(b[1])]
    end
  end

  # The linearized block-pass operand (if any), as a 1-element list to splice into `hoist`'s
  # operand sequence in eval-order position (after all args). Empty for a literal block / nil.
  def blk_operand(blk)
    blk && blk[0] == :blockpass && blk[1] ? [blk[1]] : []
  end

  # Linearize the default-value expressions inside a param list (:popt / :pkey). Defaults
  # are evaluated lazily in the callee scope, so they are recursed into (nested operand
  # jumps hoisted) but never hoisted *out* of the param list.
  def run_params(params)
    params.map do |p|
      case p[0]
      when :popt then [:popt, p[1], run(p[2])]
      when :pkey then p[2] ? [:pkey, p[1], run(p[2])] : p
      else p
      end
    end
  end

  # Linearize the value (and key) expressions inside a `[:kwargs, …]` marker.
  def run_kwargs(node)
    [:kwargs, node[1].map { |el| el[0] == :kwsplat ? [:kwsplat, el[1] && run(el[1])] : [run(el[0]), run(el[1])] }]
  end

  def run_arg(a)
    a[0] == :kwargs ? run_kwargs(a) : run(a)
  end

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
      args = node[3].map { |a| run_arg(a) }
      blk  = blk_of(node[4])
      hoist((recv ? [recv] : []) + args + blk_operand(blk)) || [:send, recv, node[2], args, blk]
    when :yield
      args = node[1].map { |a| run_arg(a) }
      hoist(args) || [:yield, args]
    when :array
      elems = node[1].map { |e| run_arg(e) }
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
    when :def   then [:def, node[1], run_params(node[2]), run(node[3])]
    when :defs  then [:defs, run(node[1]), node[2], run_params(node[3]), run(node[4])]
    when :block then blk_of(node)
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
      args = node[1].map { |a| run_arg(a) }
      blk  = blk_of(node[2])
      hoist(args + blk_operand(blk)) || [:super, args, blk]
    when :zsuper then [:zsuper, blk_of(node[1])]
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
