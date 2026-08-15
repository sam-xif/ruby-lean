# The two implicit-Array-conversion sites L133 could *not* make answer, pinned
# so the refusals stay visible. Neither is a builtin, so neither has a prelude
# twin to defer to: `spread` and `callClosure` are interpreter code, and a rule
# whose difficulty is "it has to dispatch" cannot live there.
#
# Both were **wrong answers** before L133 — the object was wrapped / bound whole
# and the `to_ary`/`to_a` never ran — so a gate here is the trade L133 made
# deliberately. Closing either means giving the interpreter a way to run a send
# mid-binding, which is the same machinery §Known wrong answers 4 wants for the
# observation.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r.gsub(/0x[0-9a-f]+/, '0xADDR')}"
end

class Good; def to_ary = [7, 8]; end
class MM;   def method_missing(n, *a); puts "  mm(#{n})"; "nope"; end; end

# splat converts with `to_a`, and a method_missing can serve it.
show("splat-mm")      { [0, *MM.new] }
# a block with >=2 parameters given one argument auto-splats it via to_ary.
show("blockarg-good") { [Good.new].each { |x, y| puts "  #{x.inspect} #{y.inspect}" }; nil }
