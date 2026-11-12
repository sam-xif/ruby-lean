# FIXED — `File.join` is `rb_file_join`.
#
# It was `parts.map { |x| x.to_s }.join("/")`, which is a different function:
# a nested Array was rendered with `Array#to_s` instead of being joined, a
# separator run was doubled (`File.join("a/", "/b")` answered `"a///b"` where
# CRuby answers `"a/b"`), and an array that contains itself ran to the fuel
# limit instead of raising `ArgumentError: recursive array`. Two of those are
# wrong answers and the third loses the whole program, so all three are pinned
# here; found while fixing the path coercion in the issue (`File.join(1, 2)`).
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

# a nested array is joined first, then treated as one component
show("nested")      { File.join(["a", ["b", ["c"]]]) }
show("array first") { File.join(["a", "b"], "c") }
show("empty array") { File.join("a", []) }
show("all empty")   { File.join([[], []]) }
show("no parts")    { File.join }
show("only empty")  { File.join("") }

# a separator run is never doubled: an element that starts with `/` replaces
# the separators collected so far, otherwise one is added only when needed
show("a/ then /b")        { File.join("a/", "/b") }
show("a then /b")         { File.join("a", "/b") }
show("a// then b")        { File.join("a//", "b") }
show("a, empty, b")       { File.join("a", "", "b") }
show("trailing empty")    { File.join("a", ["b"], "") }
show("root then a")       { File.join("/", "a") }
show("double root")       { File.join("//", "a") }
show("separators only")   { File.join("//", "//") }
show("sub-array sep")     { File.join("a/", ["/b", "c"]) }

# an element is a path, so a non-path is `no implicit conversion`
show("integer element") { File.join(["a", 1]) }
show("nested integer")  { File.join([1, [2, 3]]) }

# recursion is detected by identity, at any depth
a = []
a << a
show("self") { File.join(a) }
b = []
c = [b]
b << c
show("two-cycle") { File.join(c) }
d = ["x"]
d << [d]
show("deep") { File.join(d) }

# the same array twice is not a cycle
e = ["p", "q"]
show("shared") { File.join([e, e]) }

# controls: this is `File.join`, not `Array#join`/`String#+`
show("array join")  { ["a", ["b"]].join("/") }
show("string plus") { "a" + "/b" }
show("nested array join") { [["a"], ["b"]].join("/") }
