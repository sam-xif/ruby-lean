class G
  def method_missing(name, *)
    "G_mm:#{name}"
  end
end
module Log
  def method_missing(name, *args)
    "Log[" + super + "]"
  end
end
class G
  prepend Log
end
puts G.new.foo
puts G.new.respond_to?(:bar)
