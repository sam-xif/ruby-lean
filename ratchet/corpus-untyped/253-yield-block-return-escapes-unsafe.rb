def m
  yield
end
def h
  m { return "s" }
  1
end
h + 1
