@a = "s"
def method_missing(*n)
  @a = 1
  2
end
x
@a + "b"
