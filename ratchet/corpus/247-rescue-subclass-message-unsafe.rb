class E < StandardError
  def message
    5
  end
end
begin
  raise E
rescue StandardError => e
  e.message + "s"
end
