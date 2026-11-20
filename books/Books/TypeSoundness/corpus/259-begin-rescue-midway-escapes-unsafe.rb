# typed: true
x = 1
begin
  x = "s"
  raise "boom"
  x = 2
rescue
  nil
end
x + 1
