def run(&b)
  b.call(2)
end

run { |x| x * 3 }
