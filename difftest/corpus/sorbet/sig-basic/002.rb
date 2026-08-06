# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(x: Integer).returns(String) }
def stringify(x)
  x.to_s
end

[1, "two", 3].each do |v|
  begin
    puts stringify(T.unsafe(v))
  rescue TypeError
    puts "trapped"
  end
end
