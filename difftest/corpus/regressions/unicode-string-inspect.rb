# Native Unicode printability, named escapes and supplementary-plane escapes.
samples = [
  "\u{0}", "\u{1}", "\u{7}", "\u{8}", "\u{9}", "\u{A}", "\u{B}",
  "\u{C}", "\u{D}", "\u{1B}", "\u{1F}", "\u{20}", "\u{22}", "\u{23}",
  "\u{5C}", "\u{7E}", "\u{7F}", "\u{80}", "\u{85}", "\u{9F}", "\u{A0}",
  "\u{AD}", "\u{378}", "\u{61C}", "\u{200B}", "\u{2028}", "\u{2029}", "\u{2065}",
  "\u{FEFF}", "\u{FFFD}", "\u{FFFE}", "\u{FFFF}", "\u{10000}", "\u{1D455}", "\u{1F600}",
  "\u{1F6D8}", "\u{2FFFF}", "\u{E0000}", "\u{E0001}", "\u{E007F}", "\u{10FFFF}"
]
p samples
samples.each { |s| p [s, s.inspect, "before" + s + "after"] }
p ['#{x}', '#@x', '#$x', '"', '\\']
p [0.chr.b, 127.chr.b, 128.chr, 255.chr]
class UnicodeInspectString < String; end
p UnicodeInspectString.new("\u2028\u{1D455}é😀")
nil
