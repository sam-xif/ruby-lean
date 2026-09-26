# case/when → if-chain over `===` (C26). Subject evaluated ONCE; each `when` value tested
# `pattern === subject` in source order, short-circuit within a multi-value `when`.
def cls(x)
  case x
  when Integer then "int"
  when String, Symbol then "strsym"
  when 1..10 then "range"          # unreachable after Integer, but exercises Range#===
  else "other"
  end
end
print("i=#{cls(5)};")
print("s=#{cls('hi')};")
print("y=#{cls(:z)};")
print("o=#{cls(3.5)};")

# Value of a case expression + fall-through to else / nil.
print("val=#{(case 99 when 1 then :a end).inspect};")   # no match, no else -> nil

# Subjectless case: truth-test each condition directly (no ===).
n = 7
label = case
        when n < 0 then "neg"
        when n.even? then "even"
        else "odd"
        end
print("sub=#{label};")

# Splat in a `when` (`when *arr`): any element matches. Mixed literal+splat too, and the
# non-array coercion (`when *5` behaves like `when 5`).
def sp(x)
  arr = [2, 3, 4]
  case x
  when 1, *arr then "in"
  when *5 then "five"
  else "no"
  end
end
print("sp3=#{sp(3)};")
print("sp1=#{sp(1)};")
print("sp5=#{sp(5)};")
print("sp9=#{sp(9)};")

# Eval-order: subject once, then when-values left-to-right until a match.
def tr(x); print("#{x};"); x; end
r = case tr(:S)
    when tr(:w1) then :a
    when tr(:S) then :b
    else :c
    end
print("order=#{r}")
r
