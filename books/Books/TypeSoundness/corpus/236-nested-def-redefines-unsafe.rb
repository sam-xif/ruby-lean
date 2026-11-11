# typed: true
extend T::Sig
sig { returns(Integer) }
def bar
  1
end
sig { returns(Integer) }
def foo
  sig { returns(String) }
  def bar
    "s"
  end
  1
end
foo
bar + 1
