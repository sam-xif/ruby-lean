module Runner
  def self.twice
    yield(1) + yield(2)
  end
end


Runner.twice { |x| x * 10 }
