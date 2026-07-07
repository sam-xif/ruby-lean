def apply(&blk)
  blk.call(10)
end
square = proc { |x| x * x }
puts apply(&square)

def relay(&b)
  [1,2,3].map(&b)
end
p relay { |x| x + 100 }

def no_block_given
  yield
end
begin
  no_block_given
rescue LocalJumpError => e
  puts "LJE: #{e.message}"
end
puts no_block_given { :provided }.inspect
