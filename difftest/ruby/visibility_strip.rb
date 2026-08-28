# visibility_strip — remove access-control declarations: make a program *more
# permissive*, byte-for-byte, changing nothing else.
#
# The sig_strip argument (gradual guarantee: stripping removes *traps*), transposed
# to Ruby's visibility layer. Every form stripped here installs a trap and nothing
# but a trap:
#
#   private_constant :X       — later `A::X` reads raise NameError ("private
#                               constant"); lexical reads are unchanged. Stripping
#                               makes those reads *succeed* instead of raise.
#   private_class_method def self.m … end
#                             — external `A.m` calls raise NoMethodError.
#                               Stripping unwraps to the bare `def self.m` (the
#                               statement's own value changes from the wrapped
#                               send's to the def's `:m`; both are discarded in
#                               statement position).
#   private / public / protected (bare, or with symbol/def arguments)
#                             — set method visibility; enforcement is a
#                               dispatch-time trap on the *caller's* shape.
#
# So a certificate over the **stripped** program is a certificate for the
# annotated one, modulo exactly the visibility raises — the same shape as
# sig_strip's contract (a raise the accept criterion already excludes is the only
# behavioral delta). NoMethodError from a *private* call is a deliberate
# visibility trap, not a type error the initiative's bad-state predicate is after
# — the method exists with the right signature.
#
# What is NOT stripped: `module_function` (it *copies* methods to the eigenclass —
# structural), `public_constant` (a no-op only if nothing made it private first —
# after stripping private_constant it is vacuous, but strip it too for symmetry),
# attr_* (they define methods), include/extend of real modules (structural).
#
# I/O: source on stdin, stripped source on stdout. exit 0 = ok; 1 = parse error.
require "prism"

Edit = Struct.new(:start, :finish, :replacement)

VIS_SYMBOL_CALLS = %i[private_constant public_constant private public protected
                      private_class_method public_class_method].freeze

def statement_call?(node)
  node.is_a?(Prism::CallNode) && node.receiver.nil?
end

src = $stdin.read
result = Prism.parse(src)
unless result.success?
  warn "parse error: #{result.errors.first&.message}"
  exit 1
end

edits = []

visit = lambda do |node|
  node.child_nodes.compact.each { |c| visit.call(c) }
  next unless statement_call?(node)
  name = node.name
  next unless VIS_SYMBOL_CALLS.include?(name)
  args = node.arguments&.arguments || []
  if args.empty?
    # bare `private` etc — sets the default visibility for the rest of the body
    edits << Edit.new(node.location.start_character_offset,
                      node.location.end_character_offset, "")
  elsif args.all? { |a| a.is_a?(Prism::SymbolNode) || a.is_a?(Prism::StringNode) }
    # `private_constant :A, :B` / `private :m`
    edits << Edit.new(node.location.start_character_offset,
                      node.location.end_character_offset, "")
  elsif args.length == 1 && args.first.is_a?(Prism::DefNode)
    # `private_class_method def self.m … end` → keep just the def
    d = args.first.location
    edits << Edit.new(node.location.start_character_offset,
                      d.start_character_offset, "")
    edits << Edit.new(d.end_character_offset,
                      node.location.end_character_offset, "")
  end
end
visit.call(result.value)

# apply edits right-to-left; drop edits nested inside another edit's span
edits.sort_by! { |e| -e.start }
out = src.dup
prev_start = nil
edits.each do |e|
  next if prev_start && e.finish > prev_start
  out[e.start...e.finish] = e.replacement
  prev_start = e.start
end

# tidy: collapse lines that became blank (had only the stripped call)
out = out.lines.map { |l| l.strip.empty? && !l.empty? ? "\n" : l }.join
puts out
