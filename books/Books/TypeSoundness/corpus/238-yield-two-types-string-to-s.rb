# typed: true
extend T::Sig
sig { returns(String) }
def hello
  yield 1
  yield "str"
end


s = ""
hello { |v| 
  s += v.to_s
}

s
