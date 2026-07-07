class Proxy
  def method_missing(name, *args)
    return super unless name.to_s.start_with?("get_")
    "got:#{name}:#{args.join(',')}"
  end
  def respond_to_missing?(name, include_private = false)
    name.to_s.start_with?("get_")
  end
end
p = Proxy.new
puts p.get_foo(1, 2)
puts p.respond_to?(:get_bar)
puts p.respond_to?(:other)
begin
  p.other
rescue NoMethodError => e
  puts "NoMethodError:#{e.message.include?('other')}"
end
