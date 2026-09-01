def build(type:, name:)
  type + "/" + name
end

kw = { type: "brew", name: "x" }
build(**kw)
