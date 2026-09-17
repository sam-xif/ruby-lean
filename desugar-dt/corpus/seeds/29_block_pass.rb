# Block-pass argument `foo(&expr)` (C24): pass `expr` as the call's block. A Proc is used
# as-is; `nil` means no block; anything else is coerced via `to_proc` (the `&:sym` case).
# `&expr` is an ARGUMENT — it evaluates last, after the positional args, and coerces there.
def take
  yield 10
end

p = proc { |x| x + 1 }
print("proc=#{take(&p)};")            # &Proc used directly
print("sym=#{[1, 2, 3].map(&:to_s).inspect};")  # &:to_s -> Symbol#to_proc
print("nil=#{take { 99 } };")         # (baseline: literal block still works)

# &nil explicitly means "no block": block_given? is false
def optblk(&b)
  block_given? ? "has" : "none"
end
print("amp_nil=#{optblk(&nil)};")

# Forwarding: capture with &b, pass it on with &b — same block reaches the inner yield.
def fwd(&b)
  inner(&b)
end
def inner
  yield 7
end
print("fwd=#{fwd { |v| v * 3 }};")

# Eval-order obligation: args evaluate BEFORE the &-operand is evaluated/coerced.
def order(a)
  yield a
end
r = order((print("arg;"); 5), &(print("amp;"); proc { |x| x * 10 }))
print("r=#{r}")
r
