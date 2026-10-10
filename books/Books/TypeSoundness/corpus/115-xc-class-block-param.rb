# typed: true
class A
  extend T::Sig
  sig { params(blk: T.proc.params(v: Integer).returns(Integer)).returns(Integer) }
  def a(&blk)
    blk.call(3)
  end
end


A.new.a { |v| v }
