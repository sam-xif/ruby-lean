class Guard
  def risky
    define_singleton_method(:done) { "cleaned" }
    raise "boom"
  ensure
    puts self.done
  end
end
begin
  Guard.new.risky
rescue => e
  puts e.message
end
