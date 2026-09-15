#!/usr/bin/env ruby
# frozen_string_literal: true

# const_inline.rb — inline module-body constant *reads that happen at boot*
# with the literal the constant was assigned, when that literal is a regexp.
#
# Part of the certificate strip pipeline. The J-certificate's table cannot yet
# thread a constant *written by the program* back into later reads (the J42
# bill; `Judge.casgnM` keeps the table fixed), so `FORGES = { … =>
# TWO_SEGMENT_PATH }` is uncertifiable as written. Inlining the regexp literal
# is behavior-equal at boot up to object identity (a fresh `Regexp` per read
# site instead of one shared object; regexps are frozen in practice and the
# slice never compares them by identity). Reads inside `def`/`defs` bodies are
# NOT rewritten — those run after boot and read the real constant.
require "prism"

src = $stdin.read
result = Prism.parse(src)

# pass 1: module-body casgns whose rhs is a regexp literal → source text
literals = {}
collector = Class.new(Prism::Visitor) do
  define_method(:visit_constant_write_node) do |node|
    if node.value.is_a?(Prism::RegularExpressionNode)
      # `byteslice`, not `[]`: the offsets are byte offsets (see the binary-editing
      # note below), and a file with a multi-byte character before the literal would
      # otherwise capture a shifted span.
      literals[node.name.to_s] =
        src.byteslice(node.value.location.start_offset,
                      node.value.location.end_offset - node.value.location.start_offset)
    end
    super(node)
  end
end.new
result.value.accept(collector)

# pass 1b: module-body casgns whose rhs is a *string* literal → runtime value
# (used to fold `#{CONST}` interpolations inside regexp literals below).
strings = {}
str_collector = Class.new(Prism::Visitor) do
  define_method(:visit_constant_write_node) do |node|
    strings[node.name.to_s] = node.value.unescaped if node.value.is_a?(Prism::StringNode)
    super(node)
  end
end.new
result.value.accept(str_collector)

# pass 2: constant reads inside a casgn rhs but outside any def/defs body
edits = []
rewriter = Class.new(Prism::Visitor) do
  def initialize(literals, strings, edits)
    @literals = literals
    @strings = strings
    @edits = edits
    @in_def = 0
    @in_casgn = 0
    super()
  end
  def visit_def_node(node)
    @in_def += 1
    super(node)
    @in_def -= 1
  end
  def visit_constant_write_node(node)
    @in_casgn += 1
    super(node)
    @in_casgn -= 1
  end
  def visit_constant_read_node(node)
    if @in_def.zero? && @in_casgn.positive? && (lit = @literals[node.name.to_s])
      @edits << [node.location.start_offset, node.location.end_offset, lit]
    end
    super(node)
  end
  # `#{CONST}` inside a regexp literal, CONST a known string constant: fold the
  # string's runtime value into the regexp source (what CRuby's interpolation
  # produces at construction), turning the interpolated literal into a plain
  # one. Behavior-identical: same `Regexp#source`, same options.
  def visit_interpolated_regular_expression_node(node)
    if @in_def.zero? && @in_casgn.positive?
      node.parts.each do |part|
        next unless part.is_a?(Prism::EmbeddedStatementsNode)
        next unless part.statements && part.statements.body.length == 1
        stmt = part.statements.body[0]
        next unless stmt.is_a?(Prism::ConstantReadNode)
        if (val = @strings[stmt.name.to_s])
          @edits << [part.location.start_offset, part.location.end_offset, val]
        end
      end
    end
    super(node)
  end
end.new(literals, strings, edits)
result.value.accept(rewriter)

# Prism reports **byte** offsets and `String#[]` indexes by **characters**, so a file
# with any multi-byte character before an edit had the wrong span replaced. Editing in
# binary makes the two agree (see `difftest/ruby/require_strip.rb` for the case that
# found it, and `ruby-lean/notes/ratchet/found-issues.md`).
out = src.dup.force_encoding(Encoding::BINARY)
edits.sort_by! { |(s, _, _)| -s }
edits.each { |(s, e, lit)| out[s...e] = lit }
out = out.force_encoding(src.encoding)
print out
