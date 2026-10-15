# typed: true
extend T::Sig
sig { params(name: String, version: T.nilable(String)).returns(String) }
def build(name:, version: nil)
  version.nil? ? name : name + "@" + version
end

build(name: "x") + build(name: "x", version: "1")
