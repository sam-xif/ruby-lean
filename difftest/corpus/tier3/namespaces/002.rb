class A
  COLOR = "red"
end
class B < A
  def c; COLOR; end
end
puts B.new.c
begin
  B::COLOR
  puts "got via B"
rescue NameError => e
  puts e.class
end
puts B.ancestors.include?(A)
B.new.c
