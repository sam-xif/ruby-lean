class ExceptionName
  def to_s
    puts :name_to_s
    "DISPLAY_NAME"
  end
end
class Loud < RuntimeError
  def self.name
    puts :class_name
    ExceptionName.new
  end
  def message
    puts :message
    "MESSAGE"
  end
end
raise Loud, "quiet"
