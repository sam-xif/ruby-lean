module M
end
class Integer
  include M
end
x = 5
if x.is_a?(M)
  x + "s"
else
  1
end
