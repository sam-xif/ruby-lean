# typed: true
extend T::Sig
sig { params(type: String, name: String).returns(String) }
def build(type:, name:)
  type + "/" + name
end

kw = { type: "brew", name: "x" }
build(**kw)
