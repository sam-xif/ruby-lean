class Widget
end
Widget.class_eval do
  attr_accessor :val
  define_method(:double) { @val * 2 }
end
w = Widget.new
w.val = 7
puts w.double
puts Widget.instance_methods(false).sort.inspect
