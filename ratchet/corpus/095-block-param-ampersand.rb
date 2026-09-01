def run(&b)
  b.call(5)
end

run { |x| x + 1 }
