# Invalid arguments fail before frozen writes; missing macros stay missing.
class MixinTarget; end
[:include, :prepend, :extend].each do |op|
  [[], [String], [Object.new], [nil], [true], [false], [1], [:x]].each do |args|
    begin
      MixinTarget.send(op, *args)
    rescue => e
      p [op, e.class, e.message]
    end
  end
end
MixinTarget.freeze
[:include, :prepend, :extend].each do |op|
  begin
    MixinTarget.send(op, String)
  rescue => e
    p [op, e.class, e.message]
  end
end
begin
  include(String)
rescue => e
  p [e.class, e.message]
end
begin
  Object.new.include
rescue => e
  p [e.class, e.message]
end
begin
  BasicObject.new.__send__(:extend, String)
rescue => e
  p [e.class, e.message]
end
