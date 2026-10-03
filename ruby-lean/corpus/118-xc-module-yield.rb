# typed: true
module Runner
  extend T::Sig
  sig { params(blk: T.proc.params(arg0: Integer).returns(Integer)).returns(Integer) }
  def self.twice(&blk)
    yield(1) + yield(2)
  end
end


Runner.twice { |x| x * 10 }
