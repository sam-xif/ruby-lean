class Message
  def to_s
    p [:stringify_message, $!.nil?]
    "LOUD"
  end
end
class Loud < RuntimeError
  def message
    p [:message, $!.nil?]
    Message.new
  end
end
puts :program
raise Loud, "quiet"
