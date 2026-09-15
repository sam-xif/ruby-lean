# typed: true
extend T::Sig
sig { returns(T.untyped) }
def hello
  yield 1
  yield "str"
end


s = ""
hello { |v| 
  s += v.to_s
}

s
