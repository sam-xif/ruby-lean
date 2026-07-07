obj = Object.new
obj.instance_eval do
  @secret = 42
  def self.reveal; @secret; end
end
puts obj.reveal
puts obj.instance_variable_get(:@secret)
puts obj.instance_eval { @secret * 2 }
puts obj.singleton_methods.sort
