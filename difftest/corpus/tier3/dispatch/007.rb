class A
  def run; "A#run"; end
end
class B < A
  def run
    result = [1, 2].map { |i| "#{i}:#{super()}" }.join(",")
    ensure_val = begin
      "blk"
    ensure
      super()
    end
    "#{result}|#{ensure_val}"
  end
end
puts B.new.run
