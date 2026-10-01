class Loud < RuntimeError
  def message
    puts :message
    raise "message failed"
  ensure
    puts :message_ensure
  end
end
raise Loud, "quiet"
