def double_yield
  yield 1
  yield 2
  :method_done
end
out = []
r = double_yield do |x|
  out << x
  next "next#{x}" if x == 1
  break "break#{x}" if x == 2
end
p out
p r

def loop_break
  3.times do |i|
    2.times do |j|
      break if j == 1
      puts "#{i},#{j}"
    end
  end
  :ok
end
p loop_break
