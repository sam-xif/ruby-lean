# yield: invoke the current block; args evaluate left-to-right BEFORE the block
# body runs (eval-order obligation), plus block_given? and next.
def m
  return "no block" unless block_given?
  yield((print("a"); 1), (print("b"); 2))
end
r = m { |x, y| print("body"); next x + y }
print(r)
r
