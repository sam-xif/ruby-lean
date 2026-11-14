#!/usr/bin/env ruby
# frozen_string_literal: true

# L294: the Unicode character predicates used by CRuby's symbol.c.
# Generate the table for the pinned oracle; --verify cross-checks every Unicode
# scalar against native Module#const_defined? and String#inspect (no constants installed).
require "rbconfig"
abort "requires CRuby" unless RUBY_ENGINE == "ruby"
verify = ARGV.delete("--verify")
abort "usage: gen_unicode.rb [--verify]" unless ARGV.empty?
probe = Module.new
start = /\A[[:upper:]\p{Lt}]\z/u
ranges = []
nonprint = []
printable = /\A[[:print:]]\z/u
count = 0
(0..0x10ffff).each do |cp|
  next if (0xd800..0xdfff).cover?(cp)
  char = cp.chr(Encoding::UTF_8)
  allowed = start.match?(char)
  prints = printable.match?(char)
  if verify
    native = begin
      probe.const_defined?(char, false)
      true
    rescue NameError
      false
    end
    abort "start-character mismatch: U+#{cp.to_s(16)}" unless native == allowed
    native_prints = [34, 92].include?(cp) || char.inspect == '"' + char + '"'
    abort "printable mismatch: U+#{cp.to_s(16)}" unless native_prints == prints
  end
  if cp >= 128 && !prints
    if !nonprint.empty? && nonprint[-1][1] == cp - 1
      nonprint[-1][1] = cp
    else
      nonprint << [cp, cp]
    end
  end
  next unless allowed
  count += 1
  if !ranges.empty? && ranges[-1][1] == cp - 1
    ranges[-1][1] = cp
  else
    ranges << [cp, cp]
  end
end
warn "verified printability and constant starts for all 1,112,064 Unicode scalars; #{count} allowed starts" if verify

# `String#upcase`/`#downcase` over a UTF-8 String are a per-character,
# context-free map in this CRuby — `"ΑΣ".downcase` is `"ασ"`, not `"ας"`, so there
# is no Final_Sigma rule to model — which makes the whole behaviour two tables
# codepoint -> replacement, for the codepoints whose mapping is not the identity.
# ASCII is `Char.toUpper`/`Char.toLower` in the model, which is the same mapping.
# A replacement may be several characters (`ß` -> `SS`, `İ` -> `i̇`).
def case_table
  table = {}
  (0x80..0x10ffff).each do |cp|
    next if (0xd800..0xdfff).cover?(cp)
    char = cp.chr(Encoding::UTF_8)
    mapped = yield char
    table[cp] = mapped unless mapped == char
  end
  table
end

# A selector's mapping is the default one with a delta: `:turkic` adds the
# dotted/dotless `i` (an ASCII delta too — `i` is `İ` under it), `:fold` is full
# case folding. The delta is a whole map, so it also covers a codepoint where the
# variant is the identity but the default is not.
def case_delta(base, ascii)
  delta = {}
  (0..0x10ffff).each do |cp|
    next if (0xd800..0xdfff).cover?(cp)
    char = cp.chr(Encoding::UTF_8)
    default = base[cp] || (cp < 128 ? char.send(ascii) : char)
    variant = yield char
    delta[cp] = variant unless variant == default
  end
  delta
end

upper = case_table(&:upcase)
lower = case_table(&:downcase)
upper_turkic = case_delta(upper, :upcase) { |c| c.upcase(:turkic) }
lower_turkic = case_delta(lower, :downcase) { |c| c.downcase(:turkic) }
lower_fold = case_delta(lower, :downcase) { |c| c.downcase(:fold) }

if verify
  # A table is faithful only if mapping one character at a time is the same as
  # mapping the whole String — the assumption the Lean rule makes. Check that
  # against the oracle on the mapped characters themselves, on strings that mix
  # script and case, and on random multi-byte strings.
  rng = Random.new(20_261_111)
  strings = (upper.keys.sample(150, random: rng) + lower.keys.sample(150, random: rng))
            .map { |cp| cp.chr(Encoding::UTF_8) }
  strings += ["ΑΣ", "ΣΣΣ", "Straße", "ǅungla", "İstanbul", "ıIİi", "ﬃ ﬀ", "aäAÄ", "ä̈"]
  200.times do
    codepoints = Array.new(rng.rand(1..6)) { rng.rand(0x20..0x2ffff) }
    candidate = codepoints.map { |cp| [cp].pack("U") }.join
    strings << candidate if candidate.valid_encoding?
  end
  # The composition the Lean side performs: the delta first, then the ASCII
  # mapping, then the table.
  variants = [
    ["upcase", upper, {}, :upcase, []],
    ["downcase", lower, {}, :downcase, []],
    ["upcase(:turkic)", upper, upper_turkic, :upcase, [:turkic]],
    ["downcase(:turkic)", lower, lower_turkic, :downcase, [:turkic]],
    ["downcase(:fold)", lower, lower_fold, :downcase, [:fold]]
  ]
  variants.each do |label, table, delta, ascii, selectors|
    strings.each do |str|
      got = str.each_char.map do |c|
        delta[c.ord] || (c.ord < 128 ? c.send(ascii) : (table[c.ord] || c))
      end.join
      abort "#{label} mismatch on #{str.inspect}: #{got.inspect}" unless got == str.send(ascii, *selectors)
    end
  end
  warn "verified per-character case mapping against native upcase/downcase on #{strings.size} strings"
end

lean_string = lambda do |s|
  body = s.each_char.map do |c|
    case c
    when '"' then '\\"'
    when "\\" then "\\\\"
    when "\n" then '\\n'
    else c.ord < 0x20 || c.ord == 0x7f ? format('\\u{%X}', c.ord) : c
    end
  end.join
  "\"#{body}\""
end

# The Lean side is a lookup per character rather than a `Char -> Char` map: a
# replacement can be longer than one character. A lambda, not a `def`, for the
# reason gen_cruby_names.rb gives about `FOLD`: a `def` here would land on Object.
emit_case_tables = lambda do |tables|
  tables.each_with_index do |(name, table), i|
    puts if i.zero?
    puts <<~LEAN
      private def #{name} : List (Nat × String) := [
    LEAN
    puts table.map { |cp, s| "  (#{cp}, #{lean_string.call(s)})" }.join(",\n")
    puts "  ]"
    puts
  end
end

puts <<~LEAN
  /- Generated by scripts/gen_unicode.rb from CRuby #{RUBY_VERSION},
     Unicode #{RbConfig::CONFIG["UNICODE_VERSION"]}. Do not edit by hand.
     L294: symbol.c rb_sym_constant_char_p accepts uppercase or titlecase starts;
     subsequent UTF-8 scalars use is_identchar (all non-ASCII scalars qualify).
     Printability comes from the matching regexp property, verified against
     native String#inspect, including the U+0085 exception in string.c.
     The case-mapping tables are what native String#upcase/#downcase answer for
     one character at a time; their composition is verified against the native
     whole-String answer. -/
  -- The case-mapping tables are a few thousand literal entries; elaborating the
  -- list syntax exceeds the default recursion depth.
  set_option maxRecDepth 10000
  namespace RubyCore

  private def constantStartRanges : Array (Nat × Nat) := #[
LEAN
puts ranges.map { |lo, hi| "  (#{lo}, #{hi})" }.join(",\n")
puts <<~LEAN
  ]

  def constantStart (c : Char) : Bool :=
    if c.toNat < 128 then c.isUpper else
    constantStartRanges.any fun (lo, hi) => lo ≤ c.toNat && c.toNat ≤ hi

  def validConstantName (name : String) : Bool :=
    match name.toList with
    | [] => false
    | c :: rest => constantStart c &&
        rest.all (fun c => c.toNat ≥ 128 || c.isAlphanum || c == '_')

  private def nonprintRanges : Array (Nat × Nat) := #[
LEAN
puts nonprint.map { |lo, hi| "  (#{lo}, #{hi})" }.join(",\n")
puts <<~LEAN
  ]

  def unicodePrintable (c : Char) : Bool :=
    if c.toNat < 128 then 32 ≤ c.toNat && c.toNat < 127 else
    !nonprintRanges.any (fun (lo, hi) => lo ≤ c.toNat && c.toNat ≤ hi)

  /-- Case-mapping tables for `String#upcase`/`#downcase` and their `:turkic`
      and `:fold` selectors: `caseUpperMap`/`caseLowerMap` hold the codepoints at
      or above U+0080 whose mapping is not the identity (ASCII is
      `Char.toUpper`/`Char.toLower`, the same mapping); the rest are deltas from
      those, applied first. -/
LEAN
emit_case_tables.call([["caseUpperMap", upper], ["caseLowerMap", lower],
                       ["caseUpperTurkicMap", upper_turkic], ["caseLowerTurkicMap", lower_turkic],
                       ["caseLowerFoldMap", lower_fold]])
puts <<~LEAN
  private def caseLookup (t : List (Nat × String)) (cp : Nat) : Option String :=
    t.findSome? fun (k, v) => if k == cp then some v else none

  /-- One character's mapping: the selector delta first, then the ASCII mapping,
      then the table. A replacement may be several characters (`ß` is `SS`). -/
  private def caseChar (delta table : List (Nat × String)) (upper : Bool) (c : Char) : String :=
    match caseLookup delta c.toNat with
    | some r => r
    | none =>
      if c.toNat < 128 then
        if upper then String.singleton c.toUpper else String.singleton c.toLower
      else (caseLookup table c.toNat).getD (String.singleton c)

  /-- A case mapping over a UTF-8 String, character by character. -/
  def unicodeCase (delta table : List (Nat × String)) (upper : Bool) (s : String) : String :=
    String.join (s.toList.map (caseChar delta table upper))

  def unicodeUpper (s : String) : String := unicodeCase [] caseUpperMap true s

  def unicodeLower (s : String) : String := unicodeCase [] caseLowerMap false s

  def unicodeUpperTurkic (s : String) : String :=
    unicodeCase caseUpperTurkicMap caseUpperMap true s

  def unicodeLowerTurkic (s : String) : String :=
    unicodeCase caseLowerTurkicMap caseLowerMap false s

  def unicodeLowerFold (s : String) : String :=
    unicodeCase caseLowerFoldMap caseLowerMap false s

  end RubyCore
LEAN
