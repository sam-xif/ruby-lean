# frozen_string_literal: true

require "json"

# Serialize a RubyCore S-expression to JSON for out-of-process consumers — the
# Lean model (`ruby/lean/`) is the first. The interface is versioned so either
# side can reject a mismatch (lean-model-sketch.md §2.1, §5).
#
# Encoding: an S-expr node `[:head, ...]` becomes a JSON array whose first
# element is the head as a string; Symbols anywhere (heads, var kinds, rescue
# target kinds) become strings; nil becomes null; Integer/Float/String payloads
# pass through. Decoding is positional per head, so string-vs-symbol ambiguity
# is harmless.
module Export
  # v2 (2026-07-10): `block` gained a block-locals slot
  # (`[:block, params, locals, body]`) and a `yield` head was added.
  # v3 (2026-07-10): block passing (L1b) — block-capture params ride in the flat
  # param list as "&blk"/"&" strings (no encoding change), and the new `blockpass`
  # head (`[:blockpass, expr_or_nil]`) may occupy a send/super block slot. The Lean
  # decoder (`ruby/lean/RubyCore/Syntax.lean`) must be updated to match before
  # `--sut lean` works again (L1 blocks + L1b block passing, model side).
  # v4 (2026-07-14): M2 params (C25) — the `def`/`defs`/`block` param slot is no longer a
  # flat [String]; it is a structured list of param nodes ([:preq,…], [:popt,name,default],
  # [:prest,name?], [:pkey,name,default?], [:pkwrest,name?], [:pblock,name?]). A new
  # `[:kwargs, elems]` marker may occupy the last send/super arg slot (elem = [k,v] assoc
  # or [:kwsplat, e?]). The Lean decoder must migrate the param slot + add kwargs before
  # `--sut lean` works again. v4 also folds in the additive heads added while driving the
  # desugar to full coverage (no further format break, so no bump): `defined`, `cpath`/
  # `cpath_asgn`, `redo`/`undef`/`alias`/`for`, the `fwd` arg + `pfwd` param (`...`
  # forwarding); `case`/`when` and regex/interpolated-symbol desugar away (no new head).
  VERSION = 4

  module_function

  # Full export document: { "v": 2, "ast": <node> } as a JSON string.
  def json(core)
    JSON.generate({ "v" => VERSION, "ast" => jsonable(core) })
  end

  def jsonable(x)
    case x
    when Symbol then x.to_s
    when Array  then x.map { |e| jsonable(e) }
    when nil, Integer, String then x
    when Float
      raise ArgumentError, "non-finite Float in RubyCore: #{x}" unless x.finite?
      x
    else
      raise ArgumentError, "unexpected value in RubyCore S-expr: #{x.inspect}"
    end
  end
end
