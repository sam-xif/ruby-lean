class NilClass
  def nil?
    false
  end
end
x = nil
if x.nil?
  1
else
  x + 1
end
