# M6b (C28): regex literal -> Regexp.new(source, opts); interpolated regex; dynamic symbol.
print("match=#{('hello' =~ /l+/).inspect};")       # plain regex
print("flags=#{(/ABC/i === 'abc')};")              # ignorecase flag preserved
print("src=#{/a\/b\.c/.source.inspect};")           # escaping preserved via unescaped

x = "wor"
r = /#{x}ld/                                        # interpolated regex
print("interp=#{('world' =~ r).inspect};")

opt = /a.b/m                                        # multiline flag
print("opts=#{opt.options};")

# Interpolated (dynamic) symbol.
n = 5
print("isym=#{:"item_#{n}".inspect};")
print("isymeq=#{:"a#{1}" == :a1};")
/l+/
