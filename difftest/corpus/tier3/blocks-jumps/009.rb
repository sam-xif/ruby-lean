results = []
def gen
  return to_enum(:gen) unless block_given?
  yield 1
  yield 2
  yield 3
end
e = gen
results << e.next
results << e.next
p results

def find_first(list)
  list.each { |x| return x if x > 2 }
  nil
end
p find_first([1, 2, 3, 4])

cum = 0
[1, 2, 3].each { |x| cum += x; next if x == 2; puts "kept #{x}" }
puts cum

def reduce_break
  [1,2,3,4].inject(0) { |s, x| break s if s >= 3; s + x }
end
p reduce_break
