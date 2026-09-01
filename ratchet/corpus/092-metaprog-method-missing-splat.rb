class Ghost
  def method_missing(name, *args)
    "called"
  end
end

Ghost.new.anything_at_all
