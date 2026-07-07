class Proxy
  def initialize(t); @t = t; end
  def method_missing(n, *a)
    if @t.respond_to?(n)
      self.class.send(:define_method, n) { |*x| @t.public_send(n, *x) }
      send(n, *a)
    else
      super
    end
  end
  def respond_to_missing?(n, p=false); @t.respond_to?(n) || super; end
end
p = Proxy.new([1,2,3])
puts p.size
puts p.first
puts p.respond_to?(:size)
