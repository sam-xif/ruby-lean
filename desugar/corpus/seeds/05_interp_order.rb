# string interpolation -> to_s + concat, left-to-right evaluation
def s(tag)
  print(tag)
  tag
end

out = "x#{s("A")}y#{s("B")}z"
print("|")
print(out)
