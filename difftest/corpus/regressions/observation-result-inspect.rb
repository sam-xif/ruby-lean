# The harness's final inspect is an ordinary send on the completed program heap.
counter = 4
o = Object.new
o.define_singleton_method(:inspect) do
  counter += 1
  p [:inspect, counter, $!.nil?]
  "RESULT"
end
puts :program
o
