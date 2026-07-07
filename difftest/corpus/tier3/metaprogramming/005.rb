mod = Module.new do
  def hello; "hi from #{name_val}"; end
  def name_val; "mod"; end
end
class Recv; end
Recv.include(mod)
r = Recv.new
puts r.hello
puts Recv.include?(mod)
puts r.is_a?(mod)
