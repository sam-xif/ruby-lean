class A
  def a(&blk)
    blk.call(3)
  end
end


A.new.a { |v| v }
