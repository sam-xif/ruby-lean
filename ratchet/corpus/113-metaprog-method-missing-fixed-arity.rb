class Ghost
  def method_missing(name)
    "called " + name.to_s
  end
end

Ghost.new.anything_at_all
