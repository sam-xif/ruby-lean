# L277: effectful splat and block-argument conversions now agree.
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
