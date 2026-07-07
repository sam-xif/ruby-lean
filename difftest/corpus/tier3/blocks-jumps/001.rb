def caller_method
  p = Proc.new { return 7 }
  p.call
  puts "unreachable"
  100
end
puts caller_method

def with_block
  yield
  puts "after yield unreached"
  :done
end
puts with_block { return_val = 55; return_val }.inspect
