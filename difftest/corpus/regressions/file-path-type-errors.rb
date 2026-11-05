# Issue #57: the pure File path helpers must reject a non-String path the way
# CRuby does, rather than coercing it with `to_s`.

p File.dirname(123)
p File.basename(123)
p File.join(1, 2)
p File.extname(:sym)
p File.dirname(nil)
p File.join(true, "x")
