# frozen_string_literal: true

require "json"

# Serialize a RubyCore S-expression to JSON for out-of-process consumers — the
# Lean model (`ruby/ruby-lean/`) is the first. The interface is versioned so either
# side can reject a mismatch (`../ruby-lean/RubyCore/README.md` §Mechanization, §5).
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
  # decoder (`ruby/ruby-lean/RubyCore/Syntax.lean`) must be updated to match before
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
  # v5 (2026-08-15): `block` gained a fourth slot before the body — `declared`,
  # the names Ruby makes block-local *at parse time* because their first textual
  # assignment is inside the block (C35). `[:block, params, locals, declared, body]`.
  # Kept separate from `locals` because the two differ for `defined?`; the Lean
  # decoder merges them (it decides `defined?` from the node shape) and accepts the
  # v4 four-slot shape too, so an older AST still decodes.
  # L278/C39: additive `rat` literal head with exact numerator/denominator;
  # unlike a send, it is unaffected by constructor or constant redefinition.
  # L279/C40: additive `imag` and its `flt_bits` component preserve native
  # imaginary construction, exact fractions, signed zero and per-site identity.
  # L288/C41: optional fifth for slot retains one-target multiple assignment.
  # Four-slot for nodes remain valid and unchanged.
  VERSION = 5

  module_function

  # Full export document: { "v": 2, "ast": <node> } as a JSON string.
  def json(core, literal_namespace: "program")
    JSON.generate({ "v" => VERSION, "ast" => jsonable(core, [literal_namespace, 0]) })
  end

  def jsonable(x, literals = ["program", 0])
    case x
    when Symbol then x.to_s
    when Array
      # CRuby caches a frozen numeric literal by its syntactic occurrence.
      # Assign stable sites while exporting the normalized tree, keeping this
      # metadata out of the render/parse normal form. Prelude and program are
      # separate compilation units, hence separate namespaces.
      if x[0] == :rat || x[0] == :imag
        site = "#{literals[0]}:#{literals[1]}"
        literals[1] += 1
        return ["rat", x[1], x[2], site] if x[0] == :rat
        # JSON numbers lose -0.0 in Lean. Imaginary components are native
        # literals, so preserve their bits without an overridable unary send.
        component = x[1][0] == :flt ? ["flt_bits", [x[1][1]].pack("G").unpack1("Q>")] : jsonable(x[1], literals)
        return ["imag", component, site]
      end
      # J52: the regex-literal lowering (`::Regexp.new("src", opts)`, desugar
      # C33) exports as its own head — in CRuby the literal consults no
      # constant at runtime, and on the Lean side a dedicated head is one
      # machine step (and one `Judge` rung) instead of a class-object send.
      # (A hand-written literal `::Regexp.new("s", n)` matches too; it only
      # differs if `::Regexp` was reassigned, which the model does not chase.)
      if x[0] == :send && x[1] == [:cpath, nil, "Regexp"] && x[2] == "new" &&
         x[4].nil? && x[3].is_a?(Array) && x[3].length == 2 &&
         x[3][0].is_a?(Array) && x[3][0].length == 2 && x[3][0][0] == :str &&
         x[3][1].is_a?(Array) && x[3][1].length == 2 && x[3][1][0] == :int &&
         x[3][1][1].is_a?(Integer) && x[3][1][1] >= 0
        ["regexp_lit", x[3][0][1], x[3][1][1]]
      else
        x.map { |e| jsonable(e, literals) }
      end
    when nil, true, false, Integer, String then x
    when Float
      raise ArgumentError, "non-finite Float in RubyCore: #{x}" unless x.finite?
      x
    else
      raise ArgumentError, "unexpected value in RubyCore S-expr: #{x.inspect}"
    end
  end
end
