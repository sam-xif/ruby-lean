# L280: callbacks in scan and Chain must preserve yield and return protocols.
seen = []
s = "a1b2"
p s.scan(/([a-z])(\d)/) { |pair| seen << [pair, $1, $2]; /z/.match("z") }
p [seen, $~[0]]
e = s.enum_for(:scan, /\d/)
p [e.next, e.peek, e.next]
p(loop { e.next })
p $~[0]
# The first resume chooses the native fiber root's match environment.
def resume_from_method(e)
  /method/.match('method')
  p [e.next, $~[0]]
end
e = '3 4'.enum_for(:scan, /\d/)
resume_from_method(e)
p [e.next, $~[0]]
e = '5 6'.enum_for(:scan, /\d/)
p e.next
resume_from_method(e)
p $~[0]
p "abc".scan(/./) { |x| break [:early, x] }
e = "ab".enum_for(:scan, //)
p e.to_a
chain = Enumerator::Chain.new([0], [1, 2], ok: 3)
p [chain.to_a, chain.size, chain.inspect, chain.instance_variables, chain.respond_to?(:next)]
p chain.each { |x| break [:first, x] }
m = Module.enum_for(:new)
p m.next.class
begin
  m.next
rescue StopIteration => err
  p err.result.class
end
