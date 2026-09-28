# L280: native iteration invokes overrides and checked rewind hooks.
class CustomEnumerator < Enumerator
  def each
    yield :override
    :done
  end
end
e = CustomEnumerator.new { |y| y << :original }
p [e.next, loop { e.next }]
p CustomEnumerator.allocate.inspect
obj = Object.new
def obj.each(*args, **kw); yield [args, kw]; end
e = obj.to_enum(:each, k: 1)
p [e.to_a, e.each(2).to_a, e.each(k: 3).to_a, e.each(2, k: 3).to_a]
p e.inspect
p obj.to_enum(:each, {k: 2}).inspect
e = obj.to_enum(:each, k: 1) { |*args| args }
p e.size
e = Enumerator.new { |y| p y.yield; :finished }
e.feed(k: 1)
p e.next
p(loop { e.next })
obj = Object.new
def obj.each; yield 1; yield 2; end
def obj.rewind; puts :unexpected; end
def obj.respond_to?(name, *rest); p [:respond, name, rest]; false; end
e = obj.to_enum
p e.next
p e.rewind.equal?(e)
p e.next
obj = Object.new
def obj.each; yield 3; end
def obj.respond_to_missing?(name, *rest); p [:missing_response, name, rest]; true; end
def obj.method_missing(name, *rest); p [:missing, name, rest]; :ignored; end
e = obj.to_enum
p e.next
p e.rewind.equal?(e)
p e.next
obj = Object.new
def obj.each; yield 4; end
def obj.method_missing(name, *rest); p [:unpromised, name]; raise NoMethodError; end
p obj.to_enum.rewind.class
y = Enumerator::Yielder.allocate
begin
  y.yield
rescue => err
  p [err.class, err.message]
end
e = Enumerator.new { |y| raise StopIteration, 'user stop' }
2.times do
  begin
    e.next
  rescue StopIteration => err
    p [err.message, err.result]
  end
end
