#!/usr/bin/env ruby
# frozen_string_literal: true

# read_sigs.rb -- signatures for the emitter, read off the source with Prism
# instead of out of Sorbet's symbol table.
#
#   read_sigs.rb < annotated.rb          # -> the same JSON shape as srb_sigs.py
#
# ## Why this exists
#
# `srb_sigs.py` shells out to the Sorbet binary, which is C++ and has no wasm
# port, so the browser playground cannot run it. Shipping each corpus rung's
# stored `sigs.json` instead would work only until the user edits the program --
# which is the entire point of the page. A stale signature silently misfiles the
# derivation: rename a method and the emitter blocks with "no signature for", or
# change a `sig` and the emitter proposes the *old* declared type and `validateD`
# rejects a program the user just fixed.
#
# ## Why reading the source is legitimate, not a shortcut
#
# `Ratchet/Deriv.lean`: "a declared type cannot produce a wrong accept: it
# arrives as a field of `Deriv.defDecl`, and the checker re-checks the body at
# exactly that type. A wrong signature produces a body that fails to certify."
# Signatures are certificate *data*, re-derived on the other side. So a reader
# that is less capable than Sorbet costs completeness -- blocks and rejects --
# and can never cost soundness. That is the same contract `srb_sigs.py` already
# operates under, and its own header says so.
#
# The type grammar below is `srb_sigs.py`'s `to_ty`, ported unchanged. Note what
# that means: `to_ty` was *already* a string parser over Sorbet's printed types.
# Sorbet's contribution was resolved type strings and method owners, and inside
# this fragment -- one file, `sig` directly above `def`, flat class names -- the
# source carries both.
#
# ## What is lost, and is not faked here
#
#   * Sorbet's **verdict**. Whether Sorbet typechecks the program at all
#     (`srb_clean`, `srb_diagnostics`, a rung's `expect_sorbet`) is unanswerable
#     without Sorbet. This file reports `"sorbet": null` and
#     `"verdict": "not-checked"` rather than inventing one, so a caller cannot
#     mistake silence for approval.
#   * Resolution across files, type aliases, and inherited `sig`s declared in a
#     class this file cannot see. Inheritance *within* the file still works:
#     the emitter walks superclasses itself (`sig_for`).

require "prism"
require "json"

# --------------------------------------------------------------------------
# The type mapping, into `Ratchet/Ty.lean`'s grammar  (srb_sigs.py's `to_ty`)
# --------------------------------------------------------------------------

GROUND = {
  "Integer" => { "tag" => "int" },
  "Float" => { "tag" => "float" },
  "Symbol" => { "tag" => "sym" },
  "NilClass" => { "tag" => "nilT" },
  "TrueClass" => { "tag" => "bool" },
  "FalseClass" => { "tag" => "bool" },
  "T::Boolean" => { "tag" => "bool" },
}.freeze

# `Ty.cls` is for the builtin classes, "whose instances have no ivars this
# checker models". A *user* class's instances are `Ty.inst name <spine>`, and the
# spine is not in the signature -- it comes from the instantiation. A bare user
# class name maps to `.cls`, the known divergence `emit_deriv`'s header records.
FLAT_NAME = /\A[A-Z][A-Za-z0-9_]*\z/

def split_args(s)
  out = []
  depth = 0
  cur = +""
  s.each_char do |ch|
    depth += 1 if "([{".include?(ch)
    depth -= 1 if ")]}".include?(ch)
    if ch == "," && depth.zero?
      out << cur.strip
      cur = +""
    else
      cur << ch
    end
  end
  out << cur.strip unless cur.strip.empty?
  out
end

# A Sorbet type string to a `Ty`, or nil for "no claim made". Never raises.
def to_ty(s, untyped = "exclude")
  s = s.to_s.strip
  return nil if s.empty?
  return GROUND[s] if GROUND.key?(s)
  return untyped == "any" ? { "tag" => "any" } : nil if s == "T.untyped"
  return { "tag" => "never" } if ["T.noreturn", "T.absurd"].include?(s)
  # A `.void` return: "a value the caller may not use". `Ty.any` is the same
  # reading on the declaration side, and nothing propagates it, because `.any`
  # has no `PrimSig` row: the first send to a `.void` result blocks.
  return { "tag" => "any" } if ["Sorbet::Private::Static::Void", "void"].include?(s)

  if s.start_with?("T.nilable(") && s.end_with?(")")
    inner = to_ty(s[10..-2], untyped)
    return nil if inner.nil?

    return inner == { "tag" => "nilT" } ? inner : { "tag" => "nilable", "elem" => inner }
  end
  if s.start_with?("T.class_of(") && s.end_with?(")")
    inner = s[11..-2].strip
    return FLAT_NAME.match?(inner) ? { "tag" => "clsOf", "name" => inner } : nil
  end
  if s.start_with?("T::Array[") && s.end_with?("]")
    inner = to_ty(s[9..-2], untyped)
    return inner ? { "tag" => "arrayOf", "elem" => inner } : nil
  end
  if s.start_with?("T::Hash[") && s.end_with?("]")
    parts = split_args(s[8..-2])
    return nil unless parts.length == 2

    k, v = parts.map { |p| to_ty(p, untyped) }
    return (k && v) ? { "tag" => "hashOf", "key" => k, "val" => v } : nil
  end
  if s.start_with?("T.any(") && s.end_with?(")")
    tys = split_args(s[6..-2]).map { |p| to_ty(p, untyped) }
    return nil if tys.length != 2 || tys.any?(&:nil?)

    a, b = tys
    return a if a == b

    nil_t = { "tag" => "nilT" }
    return b == nil_t ? b : { "tag" => "nilable", "elem" => b } if a == nil_t
    return { "tag" => "nilable", "elem" => a } if b == nil_t

    return { "tag" => "union", "l" => a, "r" => b }
  end
  return { "tag" => "cls", "name" => s } if FLAT_NAME.match?(s)

  nil
end

# --------------------------------------------------------------------------
# Reading `sig { ... }` off the AST
# --------------------------------------------------------------------------

# The call chain inside a `sig` block, as {params:, ret:}. Modifiers
# (`override`, `abstract`, `overridable`, `final`, `checked`) are walked past.
# Types come out as **source text**, which is what `to_ty` consumes.
def read_sig_block(call)
  body = call.block&.body
  return nil if body.nil? || body.body.empty?

  params = nil
  ret = nil
  node = body.body.first
  while node.is_a?(Prism::CallNode)
    case node.name
    when :returns
      arg = node.arguments&.arguments&.first
      ret = arg&.slice
    when :void
      ret = "void"
    when :params
      arg = node.arguments&.arguments&.first
      if arg.is_a?(Prism::KeywordHashNode)
        params = arg.elements.filter_map do |e|
          next unless e.is_a?(Prism::AssocNode)

          [e.key.slice.delete_suffix(":"), e.value.slice]
        end
      end
    end
    node = node.receiver
  end
  { params: params || [], ret: ret }
end

# Every parameter Sorbet's symbol table lists, in order. The block is excluded,
# matching `srb_sigs.py`'s ARGUMENT reader, which skips kind "block"/`<blk>`.
# All kinds are collected, not just the required ones: the emitter compares this
# count against the desugared AST's parameter list, and a short list makes it
# report a count mismatch instead of the parameter-kind block that is the real
# reason such a def is out of the fragment.
def def_param_names(params)
  return [] if params.nil?

  out = []
  out.concat(params.requireds.map { |p| p.respond_to?(:name) ? p.name.to_s : p.slice })
  out.concat(params.optionals.map { |p| p.name.to_s })
  out << params.rest.name.to_s if params.rest.respond_to?(:name) && params.rest&.name
  out.concat(params.posts.map { |p| p.respond_to?(:name) ? p.name.to_s : p.slice })
  out.concat(params.keywords.map { |p| p.name.to_s })
  out << params.keyword_rest.name.to_s if params.keyword_rest.respond_to?(:name) && params.keyword_rest&.name
  out.compact
end

# Every `def` in the file, with the `sig` that immediately precedes it, the
# owner's flat class name, and whether the owner is one this fragment admits.
def collect(node, owner, owner_why, out)
  stmts =
    case node
    when Prism::ProgramNode then node.statements.body
    when Prism::StatementsNode then node.body
    when Prism::ClassNode, Prism::ModuleNode then node.body ? node.body.body : []
    when Prism::BeginNode then node.statements ? node.statements.body : []
    else []
    end

  prev = nil
  stmts.each do |st|
    case st
    when Prism::ClassNode, Prism::ModuleNode
      path = st.constant_path.slice
      why =
        if path.include?("::")
          "namespaced owner #{path} -- Ty.cls carries flat names here"
        elsif st.is_a?(Prism::ModuleNode)
          "module owner #{path} -- outside the fragment"
        end
      collect(st, path.split("::").last, why, out)
    when Prism::DefNode
      sig = prev.is_a?(Prism::CallNode) && prev.name == :sig ? read_sig_block(prev) : nil
      why = owner_why
      why ||= "singleton method (def self.x) -- outside the fragment" if st.receiver
      out << { owner: owner, name: st.name.to_s, line: st.location.start_line,
               def_params: def_param_names(st.parameters), sig: sig, owner_why: why }
      # A `def` inside a method body redefines at runtime, and Sorbet's symbol
      # table sees it. Missing it is not merely a lost message: rung 236 is the
      # regression test for found-issues.md F3, where exactly this redefinition
      # is what makes the program unsafe. Recursing keeps the later signature,
      # which is the one the emitter must be told about.
      collect(st.body, owner, owner_why, out) if st.body
    end
    prev = st
  end
end

# --------------------------------------------------------------------------

def main
  src = $stdin.read
  result = Prism.parse(src)
  unless result.success?
    warn(result.errors.map { |e| "#{e.location.start_line}: #{e.message}" }.join("\n"))
    puts JSON.generate({ "version" => 1, "file" => "(stdin)", "sigs" => [], "dropped" => [],
                         "reader" => "prism", "sorbet" => nil, "verdict" => "parse-error" })
    return 1
  end

  entries = []
  collect(result.value, "Object", nil, entries)

  sigs = []
  dropped = []
  entries.each do |e|
    common = { "cls" => e[:owner], "name" => e[:name], "line" => e[:line] }
    if e[:owner_why]
      dropped << common.merge("why" => e[:owner_why])
      next
    end
    # No `sig` at all reads as no declared return type -- the same drop
    # `srb_sigs.py` records when Sorbet's symbol table has no return for a method.
    if e[:sig].nil? || e[:sig][:ret].nil?
      dropped << common.merge("why" => "no declared return type")
      next
    end
    ret = to_ty(e[:sig][:ret])
    if ret.nil?
      dropped << common.merge("why" => "return type not in Ty: #{e[:sig][:ret]}")
      next
    end
    declared = e[:sig][:params].to_h
    params = []
    bad = nil
    e[:def_params].each do |pname|
      raw = declared[pname]
      if raw.nil?
        bad = "no declared type for parameter #{pname}"
        break
      end
      ty = to_ty(raw)
      if ty.nil?
        bad = "parameter #{pname} not in Ty: #{raw}"
        break
      end
      params << { "name" => pname, "ty" => ty }
    end
    if bad
      dropped << common.merge("why" => bad)
      next
    end
    sigs << common.merge("params" => params, "ret" => ret)
  end

  puts JSON.generate({
    "version" => 1, "file" => "(stdin)", "sigs" => sigs, "dropped" => dropped,
    # Sorbet did not run. Said out loud so a caller cannot read silence as approval.
    "reader" => "prism", "sorbet" => nil, "verdict" => "not-checked",
  })
  0
end

exit(main) if $PROGRAM_NAME == __FILE__
