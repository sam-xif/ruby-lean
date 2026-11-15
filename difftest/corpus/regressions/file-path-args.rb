# Issue #57: the `File` path helpers convert their path argument the way CRuby
# does — `to_path`, then `StringValue` — instead of calling `to_s`, so a
# non-String path is the `TypeError` CRuby raises rather than a string.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r}"
end

class ToPath;  def to_path = "a/b/c.txt"; end
class ToStr;   def to_str = "x/y.txt"; end
class Both;    def to_path = "p/q.txt"; def to_str = "s/t.txt"; end
class BadPath; def to_path = 5; end
class BadStr;  def to_str = 5; end
class NilPath; def to_path = nil; end
class Plain;   def to_s = "plain"; end

# `rb_get_path`: `to_path`, then `StringValue`; `to_path` wins over `to_str`,
# and its answer goes through `StringValue` too, so a non-String answer names
# the answer's class while an absent conversion names the receiver's.
show("dirname-to_path")  { File.dirname(ToPath.new) }
show("dirname-to_str")   { File.dirname(ToStr.new) }
show("dirname-both")     { File.dirname(Both.new) }
show("dirname-bad_path") { File.dirname(BadPath.new) }
show("dirname-bad_str")  { File.dirname(BadStr.new) }
show("dirname-nil_path") { File.dirname(NilPath.new) }
show("dirname-plain")    { File.dirname(Plain.new) }
show("dirname-int")      { File.dirname(123) }
show("dirname-nil")      { File.dirname(nil) }
show("dirname-true")     { File.dirname(true) }
show("basename-to_path") { File.basename(ToPath.new) }
show("basename-plain")   { File.basename(Plain.new) }
show("basename-int")     { File.basename(123) }
show("extname-to_path")  { File.extname(ToPath.new) }
show("extname-to_str")   { File.extname(ToStr.new) }
show("extname-sym")      { File.extname(:sym) }
show("extname-nil")      { File.extname(nil) }

# `basename`'s suffix is a plain `StringValue` — no `to_path` — and an explicit
# nil is refused rather than read as "no suffix".
show("basename-no_suffix")  { File.basename("a/b.txt") }
show("basename-nil_suffix") { File.basename("a/b.txt", nil) }
show("basename-int_suffix") { File.basename("a/b.txt", 1) }
show("basename-to_str")     { File.basename("a/b.txt", ToStr.new) }
show("basename-to_path")    { File.basename("a/b.txt", ToPath.new) }
show("basename-exact")      { File.basename("a/b.txt", ".txt") }
show("basename-star")       { File.basename("a/b.txt", ".*") }
show("basename-empty")      { File.basename("a/b.txt", "") }

# `File.join` flattens nested Arrays, refuses a self-referential one, converts
# each other element with `rb_get_path`, and drops the trailing separator run
# of the left side when the right side starts with one.
show("join-to_path")    { File.join(ToPath.new, "c") }
show("join-to_str")     { File.join(ToStr.new, "c") }
show("join-plain")      { File.join(Plain.new, "c") }
show("join-int")        { File.join(1, 2) }
show("join-nil")        { File.join(nil, "a") }
show("join-hash")       { File.join({ "a" => 1 }) }
show("join-array")      { File.join(["a", "b"], "c") }
show("join-nested")     { File.join([["a", ["b"]], "c"]) }
show("join-empty")      { File.join([]) }
show("join-empty_lead") { File.join([], "a") }
show("join-empty_mid")  { File.join("a", [], "b") }
show("join-array_int")  { File.join([1], 2) }
show("join-tail_slash") { File.join("a/", "b") }
show("join-lead_slash") { File.join("a", "/b") }
show("join-both_slash") { File.join("a//", "//b") }
show("join-root")       { File.join("/", "/b") }
show("join-empties")    { File.join("", "") }

cycle = ["x"]
cycle << cycle
show("join-cycle") { File.join(cycle) }
