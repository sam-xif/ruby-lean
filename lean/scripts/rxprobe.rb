# frozen_string_literal: true

# The CRuby half of the regex-engine oracle (W2a). Reads
# `pattern \t opts \t input` lines and prints the same result format
# `scripts/rxprobe.lean` prints, so the two can be diffed directly.
#
#   ruby scripts/rxprobe.rb < cases.tsv
#
# `opts` is the Regexp option word (1 IGNORECASE, 2 EXTENDED, 4 MULTILINE,
# 32 NOENCODING). Offsets are in *characters*, matching the Lean side.

def dec(s)
  s.to_s.gsub("<NL>", "\n").gsub("<TAB>", "\t")
end

$stdin.each_line do |line|
  pat, opts, inp = line.chomp("\n").split("\t", 3)
  pat = dec(pat)
  inp = dec(inp)
  begin
    re = Regexp.new(pat, opts.to_i)
  rescue RegexpError => e
    puts "ERR #{e.message}"
    next
  end
  m = re.match(inp)
  if m.nil?
    puts "nil"
  else
    caps = (1..(re.names.empty? ? m.size - 1 : m.size - 1)).map do |i|
      m.begin(i).nil? ? "-" : "#{m.begin(i)},#{m.end(i)}"
    end
    puts([m.begin(0), m.end(0), *caps].join("\t"))
  end
end
