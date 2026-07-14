# defined?(expr) → [:defined, expr] head (C26). Returns a describing String or nil; the
# argument is inspected, not (generally) evaluated. Kept as a primitive; the inner expr is
# desugared and rendered back inside `defined?(…)`.
x = 5
print("lvar=#{defined?(x)};")            # "local-variable"
print("undef=#{defined?(nope).inspect};")# nil (no such local/method)
print("ivar=#{defined?(@y).inspect};")   # nil (unset ivar)
@y = 1
print("ivar2=#{defined?(@y)};")          # "instance-variable"
print("const=#{defined?(String)};")      # "constant"
print("meth=#{defined?(puts)};")         # "method"
print("expr=#{defined?(1 + 2)};")        # "method" (Integer#+)
print("nilkw=#{defined?(nil)};")         # "expression"
print("self=#{defined?(self)};")         # "self"

# Not evaluated: a call inside defined? must not fire its side effect.
def boom; raise "should not run"; end
print("noeval=#{defined?(boom)};")       # "method", boom NOT called
defined?(x)
