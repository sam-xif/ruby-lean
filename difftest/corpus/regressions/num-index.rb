# L134 — every indexing builtin converts its subscript with `rb_num2long` (or
# `rb_to_int`), and the model gated on anything that was not already an Integer.
# CRuby answers on all of these; it is a family of messages, not a refusal.
#
# Found by R1's advisory corpus, which lost 23 of 106 programs to two of these
# rows: `Array(hash)` yields `[[k, v], …]` and the code then indexes it with
# `"type"`, so one container-shape malformation reaches both `Array#[]` and
# `Integer#[]`.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r.gsub(/0x[0-9a-f]+/, '0xADDR')}"
end

A = [10, 20, 30]

# the three distinct wordings. nil is the odd one, and it is odd *per site*:
# `rb_num2long` says "from nil to integer", `rb_to_int` (Integer#[]) says the
# ordinary "of nil into Integer".
show("a-str")      { A["x"] }
show("a-nil")      { A[nil] }
show("a-sym")      { A[:a] }
show("a-true")     { A[true] }
show("a-float")    { A[1.7] }
show("a-floatneg") { A[-1.2] }
show("a-nan")      { A[Float::NAN] }
show("a-two-str")  { A["x", 1] }
show("a-set-str")  { b = [1]; b["x"] = 5; b }

show("s-nil")      { "abc"[nil] }
show("s-sym")      { "abc"[:a] }
show("s-float")    { "abc"[1.9] }

# Integer#[] is bit reference over the two's-complement representation, so a
# negative receiver sign-extends and a negative index is 0.
show("i-str")      { 5["type"] }
show("i-nil")      { 5[nil] }
show("i-0")        { 5[0] }
show("i-1")        { 5[1] }
show("i-2")        { 5[2] }
show("i-neg")      { 5[-1] }
show("i-big")      { 5[100] }
show("i-negrecv0") { (-5)[0] }
show("i-negrecv1") { (-5)[1] }
show("i-negrecv2") { (-5)[2] }
show("i-float")    { 5[1.7] }
