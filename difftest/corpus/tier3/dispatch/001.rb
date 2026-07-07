module M
  def greet
    "M->" + super
  end
end
class C
  prepend M
  def greet
    "C"
  end
end
puts C.new.greet
puts C.ancestors.take(3).map(&:to_s).join(",")
