# File.join joins nested Arrays recursively (by identity, refusing a cycle) and
# writes a separator only where one is missing; neither rule stringifies
# anything (issue #57).
def join_case(label)
  puts label + ": " + yield.inspect
rescue StandardError => e
  puts label + ": " + [e.class, e.message].inspect
end

join_case("no arguments") { File.join }
join_case("nested arrays") { File.join(["a", "b"], "c") }
join_case("deep nesting") { File.join("a", [["b", "c"], "d"]) }
join_case("empty array") { File.join([]) }
join_case("empty array, then element") { File.join([], "c") }
join_case("empty nested array") { File.join([[], ["a"]]) }
join_case("empty strings") { File.join("", "") }

# Separators: an element starting with / replaces the trailing run in the
# result, and one that does not gets / only when the result has none.
join_case("trailing and leading separator") { File.join("a/", "/b") }
join_case("trailing run, then element") { File.join("a//", "b") }
join_case("element with leading run") { File.join("a", "//b") }
join_case("trailing separator, empty element") { File.join("a", "") }

# A non-String element is refused, never stringified.
join_case("Integer element") { File.join("a", 1) }
join_case("nil element") { File.join("a", nil) }
join_case("Hash element") { File.join({}) }
join_case("Symbol element") { File.join(:sym) }

# Only a real Array nests; a to_ary is not consulted by File.join.
class JoinToAry
  def to_ary = ["y"]
end

join_case("to_ary element") { File.join(JoinToAry.new) }

# A cycle is an ArgumentError; the same array twice is not a cycle.
shared = ["1"]
join_case("shared array") { File.join(shared, shared) }
cycle = []
cycle << cycle
join_case("self cycle") { File.join(cycle) }
outer = []
inner = [outer]
outer << inner
join_case("nested cycle") { File.join(outer) }
