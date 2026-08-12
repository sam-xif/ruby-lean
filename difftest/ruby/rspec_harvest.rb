# frozen_string_literal: true

# Turn RSpec examples into plain-Ruby assertion programs (difftest W4a / N36).
#
#   ruby rspec_harvest.rb <spec.rb>            # one JSON record per example, on stdout
#
# Why a transform and not a runner: tier 0 compares **CRuby against the model**
# on the same program, so the corpus has to be programs the model can consume —
# no RSpec, no `expect`, no metaclass tricks. And the interesting question is not
# "does Homebrew's suite pass" but "do the two executors agree", so each
# expectation is turned into *two* printed observations: the actual value, and
# the matcher's verdict. A model bug shows up in the first even when the second
# would agree.
#
# Every expectation is rewritten **by byte offset**, so an `expect` nested inside
# an `each` block or a loop is handled by the same rule as a top-level one, and
# everything we do not rewrite is carried through as its own source text.
#
# Anything the vocabulary does not cover is *reported*, never silently dropped:
# the record carries `skip` with a reason and the example's source.

require "prism"
require "json"

class Harvest
  # RSpec structure calls we understand.
  GROUPS = %w[describe context].freeze
  EXAMPLES = %w[it specify example].freeze
  MEMOS = %w[let let! subject].freeze
  # Structure calls that change what an example means, so an example inside one
  # is skipped rather than guessed at.
  POISON = %w[before after around allow double instance_double class_double
              spy stub_const allow_any_instance_of expect_any_instance_of
              shared_examples shared_context include_examples it_behaves_like
              include_context].freeze

  Example = Struct.new(:file, :line, :name, :described, :memos, :helpers, :body, :skip,
                       keyword_init: true)

  def initialize(path)
    @path = path
    @src = File.read(path)
    @res = Prism.parse(@src)
    @examples = []
    @custom_matchers = {}
  end

  def run
    raise "parse error in #{@path}" unless @res.success?

    @res.value.statements.body.each { |n| visit(n, [], [], []) }
    @examples
  end

  private

  # `RSpec.describe X do … end` at the top, `describe`/`context` inside.
  def group_call?(n)
    return false unless n.is_a?(Prism::CallNode) && n.block.is_a?(Prism::BlockNode)
    return true if GROUPS.include?(n.name.to_s) && n.receiver.nil?

    n.name.to_s == "describe" && n.receiver.is_a?(Prism::ConstantReadNode) &&
      n.receiver.name.to_s == "RSpec"
  end

  def example_call?(n)
    n.is_a?(Prism::CallNode) && n.receiver.nil? && EXAMPLES.include?(n.name.to_s)
  end

  def memo_call?(n)
    n.is_a?(Prism::CallNode) && n.receiver.nil? && MEMOS.include?(n.name.to_s) &&
      n.block.is_a?(Prism::BlockNode)
  end

  # The `described_class` a group establishes, if its first argument names one.
  def described_of(n)
    arg = n.arguments&.arguments&.first
    case arg
    when Prism::ConstantReadNode, Prism::ConstantPathNode then arg.slice
    end
  end

  def visit(n, described, memos, helpers)
    return unless n.is_a?(Prism::Node)
    return unless group_call?(n)

    inner_desc = described_of(n) || described.last
    body = n.block.body&.body || []
    # Collect this group's memos and plain `def` helpers first: RSpec makes both
    # visible to every example in the group regardless of source order. The
    # `def`s matter — the slice's specs define `vuln(data)`, `semver_range(*e)`
    # and `result(url)` that way rather than with `let`, and 68 of the 360
    # examples call them.
    local = memos + body.select { |s| memo_call?(s) }.map { |s| memo(s) }
    defs = helpers + body.grep(Prism::DefNode).map(&:slice)
    poison = body.find { |s| poisoned?(s) }
    body.each do |s|
      if example_call?(s)
        @examples << build(s, described + [inner_desc].compact, local, defs, poison)
      elsif group_call?(s)
        visit(s, described + [inner_desc].compact, local, defs)
      elsif s.is_a?(Prism::CallNode) && s.name.to_s == "matcher"
        record_custom_matcher(s)
      end
    end
  end

  def poisoned?(s)
    s.is_a?(Prism::CallNode) && s.receiver.nil? && POISON.include?(s.name.to_s)
  end

  # `let(:name) { body }` / `subject(:name) { body }` / bare `subject { body }`.
  def memo(s)
    arg = s.arguments&.arguments&.first
    name = case arg
           when Prism::SymbolNode then arg.unescaped
           else s.name.to_s == "subject" ? "subject" : nil
           end
    { "name" => name, "body" => (s.block.body&.slice || "nil"), "bang" => s.name.to_s == "let!" }
  end

  # `matcher :be_x do |args| match do |expected| … end end` — a matcher defined
  # in the spec file itself. We only need to know it exists and what its match
  # block does; `be_detected_from` (102 of the slice's 360 examples) is the one
  # that matters, and its body is a one-liner we special-case in `verdict`.
  def record_custom_matcher(s)
    arg = s.arguments&.arguments&.first
    @custom_matchers[arg.unescaped] = true if arg.is_a?(Prism::SymbolNode)
  end

  def build(node, described, memos, helpers, poison)
    line = node.location.start_line
    name = begin
      a = node.arguments&.arguments&.first
      a.is_a?(Prism::StringNode) ? a.unescaped : (a ? a.slice : "(anonymous)")
    end
    ex = Example.new(file: @path, line: line, name: name, described: described.last,
                     memos: memos, helpers: helpers, body: nil, skip: nil)
    if poison
      ex.skip = "group uses #{poison.name} (#{poison.location.start_line})"
      ex.body = node.slice
      return ex
    end
    unless node.block.is_a?(Prism::BlockNode)
      ex.skip = "example has no block"
      ex.body = node.slice
      return ex
    end

    body = node.block.body
    begin
      ex.body = rewrite(body, ex)
    rescue Unsupported => e
      ex.skip = e.message
      ex.body = node.slice
    end
    ex
  end

  class Unsupported < StandardError; end

  # Rewrite an example body by byte offset: every `expect(…).to/​not_to …` becomes
  # a call to one of the two runtime helpers, and everything else is carried
  # through verbatim.
  def rewrite(body, ex)
    return "nil" if body.nil?

    from = body.location.start_offset
    to = body.location.end_offset
    edits = []
    collect_expectations(body, edits)
    raise Unsupported, "no expectation in the example" if edits.empty?

    out = +""
    pos = from
    edits.sort_by { |e| e[:start] }.each_with_index do |e, i|
      raise Unsupported, "overlapping expectations" if e[:start] < pos

      # Prism offsets are **byte** offsets and these spec files contain
      # non-ASCII characters (em dashes in comments), so slicing `@src` by
      # character index silently shifts every rewrite after the first one.
      out << @src.byteslice(pos, e[:start] - pos)
      out << e[:make].call("#{short_id(ex)}.#{i}")
      pos = e[:stop]
    end
    out << @src.byteslice(pos, to - pos)
    # `described_class` is a *method* RSpec defines per group; the emitted
    # program has no RSpec, so it becomes a constant the preamble binds.
    out = out.gsub(/(^|[^\w.:])described_class\b/) { "#{Regexp.last_match(1)}DESCRIBED_CLASS" }
             .gsub("__DESCRIBED", "DESCRIBED_CLASS")
    raise Unsupported, "example needs described_class but its group names none" if
      out.include?("DESCRIBED_CLASS") && ex.described.nil?

    check_residue!(out, ex)
    out
  end

  def short_id(ex)
    "L#{ex.line}"
  end

  # Nothing RSpec-shaped may survive into the emitted program. `subject` is
  # allowed exactly when the enclosing groups define one, because then the
  # preamble emits it as an ordinary method.
  def check_residue!(text, ex)
    bad = %w[expect is_expected allow double instance_double described_class]
    bad << "subject" unless ex.memos.any? { |mm| mm["name"] == "subject" }
    bad.each do |b|
      next unless text =~ /(^|[^\w.:])#{Regexp.escape(b)}\b/

      raise Unsupported, "unrewritten `#{b}` in the body"
    end
  end

  def collect_expectations(node, edits)
    return unless node.is_a?(Prism::Node)

    if expectation?(node)
      edits << { start: node.location.start_offset, stop: node.location.end_offset,
                 make: make_expectation(node) }
      return # do not descend: the whole expectation is consumed
    end
    node.compact_child_nodes.each { |c| collect_expectations(c, edits) }
  end

  def expectation?(n)
    n.is_a?(Prism::CallNode) && %w[to not_to to_not].include?(n.name.to_s) &&
      n.receiver.is_a?(Prism::CallNode) &&
      %w[expect is_expected].include?(n.receiver.name.to_s)
  end

  def make_expectation(n)
    negated = n.name.to_s != "to"
    subject = n.receiver
    matcher = n.arguments&.arguments&.first
    raise Unsupported, "expectation with no matcher" if matcher.nil?

    if subject.name.to_s == "is_expected"
      actual = "subject"
      block_form = false
    elsif subject.block.is_a?(Prism::BlockNode)
      actual = subject.block.body&.slice || "nil"
      block_form = true
    else
      a = subject.arguments&.arguments&.first
      raise Unsupported, "expect() with no argument" if a.nil?

      actual = a.slice
      block_form = false
    end

    mname = matcher.is_a?(Prism::CallNode) ? matcher.name.to_s : nil
    if mname == "raise_error" || (block_form && mname.nil?)
      cls = matcher.arguments&.arguments&.first
      klass = cls.is_a?(Prism::ConstantReadNode) || cls.is_a?(Prism::ConstantPathNode) ? cls.slice : "nil"
      return ->(label) { "__exr(#{label.inspect}, -> { #{actual} }, #{klass}, #{negated})" }
    end
    raise Unsupported, "block-form expect with matcher #{mname}" if block_form

    vd = verdict(matcher)
    vd = "!(#{vd})" if negated
    ->(label) { "__exp(#{label.inspect}, -> { #{actual} }, ->(__a) { #{vd} })" }
  end

  # A matcher argument as an expression. A brace-less hash (`eq(a: 1, b: 2)`)
  # is only valid in argument position, so it has to be re-braced before it can
  # sit on the right of `==`.
  def arg_src(node)
    node.is_a?(Prism::KeywordHashNode) ? "{ #{node.slice} }" : node.slice
  end

  # The matcher, as a Ruby expression over `__a` (the actual value).
  def verdict(m)
    raise Unsupported, "non-call matcher #{m.class}" unless m.is_a?(Prism::CallNode)

    name = m.name.to_s
    args = m.arguments&.arguments || []
    arg1 = args.first && arg_src(args.first)

    # `be > x` / `be < x` / `be >= x` parse as an operator call on a bare `be`.
    if m.receiver.is_a?(Prism::CallNode) && m.receiver.name.to_s == "be" &&
       (m.receiver.arguments&.arguments || []).empty?
      raise Unsupported, "be-operator #{name}" unless %w[> < >= <= == !=].include?(name)

      return "__a #{name} (#{arg1})"
    end
    raise Unsupported, "matcher with a receiver (#{m.slice[0, 40]})" unless m.receiver.nil?

    case name
    when "eq" then "__a == (#{arg1})"
    when "eql" then "__a.eql?(#{arg1})"
    when "equal" then "__a.equal?(#{arg1})"
    when "be"
      raise Unsupported, "bare `be` with no argument" if arg1.nil?

      "__a.equal?(#{arg1})"
    when "be_nil" then "__a.nil?"
    when "be_a", "be_an", "be_kind_of", "be_instance_of" then "__a.is_a?(#{arg1})"
    when "respond_to" then "__a.respond_to?(#{arg1})"
    when "include" then args.map { |a| "__a.include?(#{arg_src(a)})" }.join(" && ")
    when "match" then "__a.match?(#{arg1})"
    when "contain_exactly"
      "__a.length == #{args.length} && " +
        args.map { |a| "__a.include?(#{arg_src(a)})" }.join(" && ")
    when "have_attributes"
      kw = args.first
      raise Unsupported, "have_attributes without a keyword hash" unless kw.is_a?(Prism::KeywordHashNode)

      kw.elements.map do |el|
        raise Unsupported, "have_attributes element" unless el.is_a?(Prism::AssocNode)

        "__a.#{el.key.unescaped} == (#{el.value.slice})"
      end.join(" && ")
    when "be_detected_from"
      # The spec file's own matcher: `expect(v).to be_detected_from(url, **specs)`
      # means `described_class.detect(url, **specs) == v`.
      inner = args.map { |a| a.is_a?(Prism::KeywordHashNode) ? a.slice : a.slice }.join(", ")
      "__DESCRIBED.detect(#{inner}) == __a"
    else
      # `be_foo` is RSpec's predicate form: `__a.foo?`.
      raise Unsupported, "matcher #{name}" unless name.start_with?("be_")

      pred = name.delete_prefix("be_")
      args.empty? ? "__a.#{pred}?" : "__a.#{pred}?(#{args.map(&:slice).join(', ')})"
    end
  end
end

path = ARGV[0] or abort "usage: rspec_harvest.rb <spec.rb>"
Harvest.new(path).run.each do |ex|
  puts JSON.generate({
    "file" => ex.file, "line" => ex.line, "name" => ex.name,
    "described" => ex.described, "memos" => ex.memos,
    "helpers" => ex.helpers, "body" => ex.body, "skip" => ex.skip,
  })
end
