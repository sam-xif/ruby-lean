# freeze_strip — remove `.freeze` calls: make a program *more permissive*,
# byte-for-byte, changing nothing else.
#
# The sig_strip/visibility_strip argument, third instance. `x.freeze` returns
# `x` (so every read of the expression's value is unchanged) and installs a
# trap: later mutations of the object raise FrozenError. Stripping removes the
# trap and nothing else — the stripped program behaves identically except that
# mutations the frozen program would have refused now succeed. A certificate
# over the stripped program is therefore a certificate for the frozen one,
# modulo exactly the FrozenError raises (which the accept criterion's bad-state
# predicate — uncaught NoMethodError/ArgumentError/TypeError — never counts).
#
# Only *literal-receiver* `.freeze` is stripped (`{…}.freeze`, `[…].freeze`,
# `"…".freeze`, integer/symbol receivers): there the value identity is
# syntactically evident. A `.freeze` on a computed receiver is left alone (the
# stripped-vs-annotated relation should stay checkable by eye).
#
# I/O: source on stdin, stripped source on stdout. exit 0 = ok; 1 = parse error.
require "prism"

LITERALS = [Prism::HashNode, Prism::ArrayNode, Prism::StringNode,
            Prism::SymbolNode, Prism::IntegerNode, Prism::FloatNode,
            Prism::RegularExpressionNode, Prism::InterpolatedStringNode].freeze

src = $stdin.read
result = Prism.parse(src)
unless result.success?
  warn "parse error: #{result.errors.first&.message}"
  exit 1
end

edits = []
visit = lambda do |node|
  node.child_nodes.compact.each { |c| visit.call(c) }
  next unless node.is_a?(Prism::CallNode) && node.name == :freeze &&
              node.arguments.nil? && node.block.nil? && node.receiver &&
              LITERALS.any? { |k| node.receiver.is_a?(k) }
  # delete from the end of the receiver to the end of the call (the ".freeze")
  edits << [node.receiver.location.end_character_offset,
            node.location.end_character_offset]
end
visit.call(result.value)

edits.sort_by! { |e| -e[0] }
out = src.dup
edits.each { |s, f| out[s...f] = "" }
puts out
