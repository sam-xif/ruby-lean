def only_positional(x = :default)
  x
end
empty = {}
p only_positional(**empty)
full = {y: 1}
p only_positional(**full)
