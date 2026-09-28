# L280: rewind abandons the suspended ensure, exceptions restart the producer.
events = []
e = Enumerator.new do |y|
  events << :start
  y << 1
  y << 2
ensure
  events << :ensure
end
p [e.next, events]
p [e.rewind.equal?(e), events]
p [e.next, events]
begin
  e.dup
rescue => err
  p [err.class, err.message]
end
e = Enumerator.new { |y| y << :value; raise "failure" }
4.times do
  begin
    p e.next
  rescue => err
    p [err.class, err.message]
  end
end
obj = Object.new
def obj.each; yield 5; :end; end
def obj.rewind; puts :rewinding; :discard; end
e = obj.to_enum
p e.next
p e.rewind.equal?(e)
p e.next
e = 2.times
e.feed(nil)
begin
  e.feed(1)
rescue => err
  p [err.class, err.message]
end
p [e.next, e.next]
