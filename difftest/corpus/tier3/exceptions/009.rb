class AppError < StandardError
  def initialize(code)
    @code = code
    super("code=#{code}")
  end
  attr_reader :code
end
begin
  raise AppError.new(42)
rescue AppError => e
  puts e.message
  puts e.code
  puts(e.is_a?(StandardError))
end
