# ADVERSARIAL (control-flow corners the round-trip must preserve):
#
# 1. `ensure` always runs, and a `return` in `ensure` OVERRIDES a pending return from the
#    body (artifact 04 §5). Correct value: 2, not 1. A desugaring that dropped the ensure
#    return, or reordered it, would disagree.
def ensure_wins
  return 1
ensure
  return 2
end
print("ensure_wins=#{ensure_wins};")

# 2. Bare `rescue` matches StandardError, NOT Exception. A raised Exception must ESCAPE the
#    bare rescue (artifact 04 §5). Here the inner bare rescue does NOT catch it; the outer
#    typed `rescue Exception` does. Correct trace: "inner-skipped-outer;".
begin
  begin
    raise Exception, "hard"
  rescue
    print("inner-caught;")   # must NOT print
  end
rescue Exception => e
  print("inner-skipped-outer;")
end

# 3. `retry` re-runs the begin body. Bounded by a counter so it terminates.
attempts = 0
begin
  attempts += 1
  print("try#{attempts};")
  raise "again" if attempts < 3
rescue
  retry if attempts < 3
end
print("settled=#{attempts}")
