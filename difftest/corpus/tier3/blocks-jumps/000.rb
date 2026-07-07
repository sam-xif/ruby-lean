def make_proc
  Proc.new { return 42 }
end
def make_lambda
  lambda { return 99 }
end
def run_lambda
  l = make_lambda
  x = l.call
  puts "lambda returned #{x}"
  :after_lambda
end
puts run_lambda.inspect
begin
  p = make_proc
  puts p.call
rescue LocalJumpError => e
  puts "LocalJumpError: #{e.message}"
end
