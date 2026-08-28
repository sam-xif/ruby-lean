#!/usr/bin/env ruby
# frozen_string_literal: true

# class_sugar_strip.rb — expand `attr_reader`/`attr_writer`/`attr_accessor`
# and `alias` inside class/module bodies into the plain `def`s they abbreviate.
#
# Part of the certificate strip pipeline. The J-certificate covers plain `def`s
# in fresh-class bodies (`Judge.defForget`, install-and-forget), but not the
# reflective installers: `attr_*` is a multi-step builtin (a composition bill),
# and `alias`'s miss branch raises `NameError`, which the invariant's control
# grammar has no mode for (`CtlOkJ.jump _ => False`) — typing it needs an
# installed-methods table channel (recorded bill). The expansions:
#
#   attr_reader :a, :b   =>  def a = @a           (one per name)
#   attr_writer :a       =>  def a=(v); @a = v; end
#   attr_accessor :a     =>  both
#   alias new old        =>  def new(...) = old(...)
#
# Behavior deltas, argued acceptable per hunk: `attr_*` returns an array of
# installed names (the expansion's last `def` returns a Symbol) — discarded in
# statement position, which is every use in the slice; `alias` captures the
# *current* definition while the delegating `def` late-binds — equal unless the
# aliased method is later redefined or the class subclassed, neither of which
# the slice does; reflective arity of `def new(...)` differs from the alias.
require "prism"

src = $stdin.read
result = Prism.parse(src)
edits = []
visitor = Class.new(Prism::Visitor) do
  define_method(:visit_call_node) do |node|
    if node.receiver.nil? && %i[attr_reader attr_writer attr_accessor].include?(node.name) &&
       node.arguments && node.arguments.arguments.all? { |a| a.is_a?(Prism::SymbolNode) }
      names = node.arguments.arguments.map(&:unescaped)
      defs = []
      names.each do |n|
        defs << "def #{n} = @#{n}" if %i[attr_reader attr_accessor].include?(node.name)
        defs << "def #{n}=(v)\n  @#{n} = v\nend" if %i[attr_writer attr_accessor].include?(node.name)
      end
      indent = " " * node.location.start_column
      edits << [node.location.start_offset, node.location.end_offset,
                defs.join("\n#{indent}")]
    end
    super(node)
  end
  define_method(:visit_alias_method_node) do |node|
    if node.new_name.is_a?(Prism::SymbolNode) && node.old_name.is_a?(Prism::SymbolNode)
      newn = node.new_name.unescaped
      oldn = node.old_name.unescaped
      edits << [node.location.start_offset, node.location.end_offset,
                oldn.match?(/\A[a-z_][A-Za-z0-9_]*[?!]?\z/) ? "def #{newn}(...) = #{oldn}(...)" : "def #{newn}(...) = self.#{oldn}(...)"]
    end
    super(node)
  end
  # `X = Struct.new(:a, :b, keyword_init: true)` => an explicit class with
  # keyword initializer + accessors. Covers the slice's used surface (`.new`
  # with keywords, field readers); Struct's `==`/`to_a`/`members`/pattern
  # matching are NOT reproduced (unused in the slice — grep before relying).
  define_method(:visit_constant_write_node) do |node|
    v = node.value
    if v.is_a?(Prism::CallNode) && v.name == :new &&
       v.receiver.is_a?(Prism::ConstantReadNode) && v.receiver.name == :Struct &&
       v.arguments
      args = v.arguments.arguments
      syms = args.take_while { |a| a.is_a?(Prism::SymbolNode) }.map(&:unescaped)
      rest = args.drop(syms.length)
      kw_init = rest.length == 1 && rest[0].is_a?(Prism::KeywordHashNode) &&
                rest[0].elements.length == 1 &&
                rest[0].elements[0].key.unescaped == "keyword_init" &&
                rest[0].elements[0].value.is_a?(Prism::TrueNode)
      if kw_init && syms.any?
        indent = " " * node.location.start_column
        nl = "\n"
        body = +"class #{node.name}#{nl}"
        syms.each do |s2|
          body << "#{indent}  def #{s2} = @#{s2}#{nl}"
          body << "#{indent}  def #{s2}=(v)#{nl}#{indent}    @#{s2} = v#{nl}#{indent}  end#{nl}"
        end
        body << "#{indent}  def initialize(#{syms.map { |s2| "#{s2}: nil" }.join(", ")})#{nl}"
        syms.each { |s2| body << "#{indent}    @#{s2} = #{s2}#{nl}" }
        body << "#{indent}  end#{nl}#{indent}end"
        edits << [node.location.start_offset, node.location.end_offset, body]
      end
    end
    super(node)
  end
end.new
result.value.accept(visitor)
out = src.dup
edits.sort_by! { |(s, _, _)| -s }
edits.each { |(s, e, r)| out[s...e] = r }
print out
