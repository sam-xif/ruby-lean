# L280: Kernel identity and a closure used both as a block and a method body.
[nil, false, true, 1, 1.5, :s, "s", [], {}, Object.new].each do |value|
  p value.itself.equal?(value)
end
p "é".b.itself.bytes
begin
  1.itself(:extra)
rescue => err
  p [err.class, err.message]
end
class IdentityBody
  prepend(Module.new do
    def itself
      body = -> { "block->" + super() }
      @text.define_singleton_method(:itself, &body)
      body
    end
  end)
  attr_reader :text
  def initialize; @text = "singleton#itself"; end
  def itself; "IdentityBody#itself"; end
end
obj = IdentityBody.new
body = obj.itself
p [body.call, obj.text.itself, body.call]
