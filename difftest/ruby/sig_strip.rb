# sig_strip — make a Sorbet-annotated program *less precise*, byte-for-byte.
#
# This is the `e ⊑ e'` transform of the gradual guarantee (Siek/Vitousek/Cimini/
# Boyland; ../docs/semantics/types-and-preservation.md §B.5 and §C.3 step 1):
# strip the annotations, change nothing else. The guarantee predicts that the
# stripped program behaves identically *except* that it traps fewer errors, so
# any other difference is either a Sorbet-runtime bug or a defect in our
# understanding of it. Either is worth knowing.
#
# What is stripped (§A.3's assertion table, all of whose forms are erasable):
#   sig { … } / sig do … end / sig { … }.checked(:never)   → deleted
#   extend/include T::Sig                                   → deleted
#   T.let(e, τ) T.cast(e, τ) T.must(e) T.unsafe(e)
#   T.assert_type!(e, τ) T.reveal_type(e)                   → e
#   T.bind(self, τ)                                         → self
#
# What is NOT strippable, and is therefore *gated* (exit 3) rather than
# mangled: T::Struct, T::Enum, T::Array[…] in a value position, type_member,
# T.absurd, and any other surviving reference to the `T` namespace. Those are
# structural — the class hierarchy and the DSL-generated methods are part of
# the program's behavior, so removing them would not produce a less-precise
# variant of the same program, it would produce a different program. Gating
# keeps the probe's relation honest (same discipline as every other fragment
# gate in this engine: declare, never silently degrade).
#
# `require "sorbet-runtime"` is deliberately KEPT. The two variants must differ
# only in annotation precision; dropping the require would also change what is
# loaded.
#
# I/O: source on stdin, stripped source on stdout.
#   exit 0 = stripped;  exit 1 = parse error;  exit 3 = unstrippable (reason on
#   stderr).

require "prism"

STRIP_TO_FIRST_ARG = %i[let cast must unsafe assert_type! reveal_type].freeze

# An edit is [start, finish, replacement_or_nil]; nil deletes the whole
# statement line. Offsets are **character** offsets, not Prism's default byte
# offsets: every splice below uses Ruby's `String#[]`, which indexes by
# character. A single non-ASCII byte anywhere earlier in the file (a `§` in a
# comment was how this surfaced) desynchronizes the two and silently corrupts
# the output.
Edit = Struct.new(:start, :finish, :replacement)

# True for `sig { … }` and for the chained `sig { … }.checked(:never)` /
# `.on_failure(…)` forms: walk down the receiver chain and see if it bottoms
# out at a block-carrying bare `sig`.
def sig_call?(node)
  return false unless node.is_a?(Prism::CallNode)
  return true if node.receiver.nil? && node.name == :sig && node.block
  node.receiver ? sig_call?(node.receiver) : false
end

def const_t?(node)
  node.is_a?(Prism::ConstantReadNode) && node.name == :T
end

# `extend T::Sig` / `include T::Sig`
def extend_t_sig?(node)
  return false unless node.is_a?(Prism::CallNode)
  return false unless node.receiver.nil? && %i[extend include].include?(node.name)
  args = node.arguments&.arguments || []
  args.length == 1 &&
    args[0].is_a?(Prism::ConstantPathNode) &&
    const_t?(args[0].parent) &&
    args[0].name == :Sig
end

class Collector < Prism::Visitor
  attr_reader :edits

  def initialize(source)
    @source = source
    @edits = []
    super()
  end

  # `X = T.type_alias { … }` — Sorbet-only: the constant exists solely to be
  # referenced inside sigs, which this transform removes. Deleting the whole
  # assignment is behavior-preserving for code whose only reads of X are in
  # (removed) sigs; the fixpoint checker flags any remaining runtime read.
  def visit_constant_write_node(node)
    v = node.value
    if v.is_a?(Prism::CallNode) && const_t?(v.receiver) && v.name == :type_alias
      @edits << Edit.new(node.location.start_character_offset,
                         node.location.end_character_offset, nil)
      return
    end
    super
  end

  def visit_call_node(node)
    if sig_call?(node) || extend_t_sig?(node)
      @edits << Edit.new(node.location.start_character_offset, node.location.end_character_offset, nil)
      return # do not descend: the whole statement is going away
    end

    if const_t?(node.receiver)
      args = node.arguments&.arguments || []
      if STRIP_TO_FIRST_ARG.include?(node.name) && args.length >= 1
        inner = args[0].location
        @edits << Edit.new(node.location.start_character_offset,
                           node.location.end_character_offset,
                           @source[inner.start_character_offset...inner.end_character_offset])
        return
      elsif node.name == :bind && args.length >= 1
        @edits << Edit.new(node.location.start_character_offset,
                           node.location.end_character_offset, "self")
        return
      end
      # anything else on `T` is left alone; the fixpoint check below gates it
    end

    super
  end
end

# Delete a whole statement: widen the range to swallow the line when nothing
# but whitespace surrounds it, so stripping leaves no blank-line litter and no
# dangling indentation.
def widen_to_line(source, start_off, end_off)
  s = start_off
  s -= 1 while s > 0 && source[s - 1] != "\n" && source[s - 1].match?(/\s/)
  return [start_off, end_off] unless s.zero? || source[s - 1] == "\n"

  e = end_off
  e += 1 while e < source.length && source[e] != "\n" && source[e].match?(/\s/)
  return [start_off, end_off] unless e >= source.length || source[e] == "\n"

  [s, [e + 1, source.length].min]
end

def strip_once(source)
  result = Prism.parse(source)
  unless result.success?
    warn(result.errors.map { |e| "#{e.location.start_line}: #{e.message}" }.join("; "))
    exit 1
  end
  collector = Collector.new(source)
  result.value.accept(collector)
  return source if collector.edits.empty?

  out = source.dup
  # apply back-to-front so earlier offsets stay valid
  collector.edits.sort_by { |e| -e.start }.each do |edit|
    if edit.replacement.nil?
      s, e = widen_to_line(out, edit.start, edit.finish)
      out[s...e] = ""
    else
      out[edit.start...edit.finish] = edit.replacement
    end
  end
  out
end

# Nested annotations (`T.must(T.cast(x, Integer))`) need more than one pass,
# because an edit's replacement is raw source text that may itself contain
# annotations. Iterating to a fixpoint is simpler and more obviously correct
# than ordering nested edits.
def strip(source)
  10.times do
    stripped = strip_once(source)
    return stripped if stripped == source

    source = stripped
  end
  warn("sig_strip did not reach a fixpoint in 10 passes")
  exit 1
end

# Gate: any surviving reference to the `T` namespace, or a surviving bare
# `sig`, means the program is not fully strippable.
def unstrippable_reasons(source)
  result = Prism.parse(source)
  return ["stripped source no longer parses"] unless result.success?

  found = []
  finder = Class.new(Prism::Visitor) do
    define_method(:visit_constant_read_node) do |node|
      found << "T" if node.name == :T
      super(node)
    end
    define_method(:visit_constant_path_node) do |node|
      found << "T::#{node.name}" if const_t?(node.parent)
      super(node)
    end
    define_method(:visit_call_node) do |node|
      found << "T.#{node.name}" if const_t?(node.receiver)
      found << "sig" if node.receiver.nil? && node.name == :sig && node.block
      super(node)
    end
  end.new
  result.value.accept(finder)
  found.uniq
end

source = $stdin.read
stripped = strip(source)
reasons = unstrippable_reasons(stripped)
unless reasons.empty?
  warn("unstrippable Sorbet constructs remain: #{reasons.join(', ')}")
  exit 3
end
print stripped
