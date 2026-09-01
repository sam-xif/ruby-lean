def build(name:, version: nil)
  version.nil? ? name : name + "@" + version
end

build(name: "x") + build(name: "x", version: "1")
