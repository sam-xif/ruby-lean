class C
  X = 1
  class D
    def look; X; end
  end
end
module M
  Y = 2
  class C
    def look2; Y; end
  end
end
puts C::D.new.look
puts M::C.new.look2
puts defined?(C::X)
puts defined?(Undefined_const)
C::X
