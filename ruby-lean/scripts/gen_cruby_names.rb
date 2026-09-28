#!/usr/bin/env ruby
# frozen_string_literal: true

# Regenerate RubyCore/CRubyNames.lean from the pinned CRuby oracle:
#
#   "$(brew --prefix ruby)/bin/ruby" scripts/gen_cruby_names.rb > RubyCore/CRubyNames.lean
#
# Emits, for each bootstrap class of the L0 Lean model, the method names
# CRuby defines directly on it (instance + private instance), folding in the
# modules the L0 ancestor chain omits (Kernel→Object, Comparable/Numeric→
# numerics/strings/symbols, Enumerable→Array/Hash), plus Object.constants.
# The Lean model uses these for dispatch fidelity (shadow detection and
# genuine-NoMethodError classification), not behavior.

FOLD = {
  "BasicObject" => [BasicObject],
  "Object" => [Object, Kernel],
  "Module" => [Module],
  "Class" => [Class],
  "NilClass" => [NilClass],
  "TrueClass" => [TrueClass],
  "FalseClass" => [FalseClass],
  "Integer" => [Integer, Numeric, Comparable],
  "Float" => [Float, Numeric, Comparable],
  "Rational" => [Rational, Numeric, Comparable],
  "Complex" => [Complex, Numeric, Comparable],
  "Enumerator" => [Enumerator, Enumerable],
  "Enumerator::Generator" => [Enumerator::Generator, Enumerable],
  "Enumerator::Yielder" => [Enumerator::Yielder],
  "Enumerator::Chain" => [Enumerator::Chain, Enumerator, Enumerable],
  "String" => [String, Comparable],
  "Symbol" => [Symbol, Comparable],
  "Array" => [Array, Enumerable],
  "Hash" => [Hash, Enumerable],
  "Proc" => [Proc],
  "Range" => [Range, Enumerable],
  "Random" => [Random],
  "Exception" => [Exception],
  # Exception subclasses in the bootstrap heap: each may add its own methods
  # (e.g. NameError#receiver, NoMethodError#args) that dispatch must know
  # exist so an unmodeled one gates instead of mis-raising NoMethodError.
  "StandardError" => [StandardError],
  "RuntimeError" => [RuntimeError],
  "ArgumentError" => [ArgumentError],
  "TypeError" => [TypeError],
  "NameError" => [NameError],
  "NoMethodError" => [NoMethodError],
  "ZeroDivisionError" => [ZeroDivisionError],
  "LocalJumpError" => [LocalJumpError],
  "FrozenError" => [FrozenError],
  "IndexError" => [IndexError],
  "KeyError" => [KeyError],
  "RangeError" => [RangeError],
  "StopIteration" => [StopIteration],
  "NotImplementedError" => [NotImplementedError],
  "ScriptError" => [ScriptError],
}.freeze

# A lambda, not a toplevel def — a def here would land on Object and leak
# into the very tables we are snapshotting. Same reason FOLD is filtered
# out of the constants list below.
NAME_LINES = lambda do |names, indent|
  names.each_slice(8).map { |sl| indent + sl.map { |s| s.to_s.inspect }.join(", ") }.join(",\n")
end

puts <<~HEADER
  /-
  GENERATED from the CRuby oracle (#{RUBY_DESCRIPTION.split.first(2).join(" ")}) by
  `scripts/gen_cruby_names.rb` — do not hand-edit. Regenerate when the
  oracle version bumps.

  Purpose (dispatch fidelity, not behavior): the L0 model implements only a
  slice of each core class, but lookup must know which names EXIST in CRuby
  so that (a) an unmodeled builtin that would shadow a user method on Object
  gates as Unsupported instead of mis-dispatching, and (b) a genuine
  lookup-total-miss can be answered with a real NoMethodError.

  Modules our L0 ancestors chain omits are folded into the nearest class
  below them: Kernel→Object, Comparable→String/Symbol/Integer/Float,
  Numeric→Integer/Float, Enumerable→Array/Hash.
  -/
  namespace RubyCore

  /-- Method names each bootstrap class defines directly in CRuby
      (instance_methods(false) ∪ private_instance_methods(false), modules
      folded as above). -/
  def crubyMethodNames : List (String × List String) := [
HEADER

# Toplevel `public`/`private`/`include`/`using`/`define_method` etc. live on
# main's singleton class; fold them into Object so a program using them
# gates as unmodeled instead of mis-raising NoMethodError.
MAIN_SINGLETON = TOPLEVEL_BINDING.receiver.singleton_class
  .then { |sc| sc.instance_methods(false) + sc.private_instance_methods(false) }

entries = FOLD.map do |name, mods|
  meths = mods.flat_map { |m| m.instance_methods(false) + m.private_instance_methods(false) }
  meths += MAIN_SINGLETON if name == "Object"
  meths = meths.uniq.sort
  "  (\"#{name}\", [\n#{NAME_LINES.call(meths, "    ")}\n  ])"
end
puts entries.join(",\n")

puts <<~MID
  ]

  /-- Singleton (class-side) method names each bootstrap class defines in
      CRuby (e.g. Hash.ruby2_keywords_hash, Array.[]): a send to a class
      object resolving past these must gate. -/
  def crubySingletonNames : List (String × List String) := [
MID
sentries = FOLD.map do |name, mods|
  meths = mods.first.singleton_class
    .then { |sc| sc.instance_methods(false) + sc.private_instance_methods(false) }.uniq.sort
  "  (\"#{name}\", [\n#{NAME_LINES.call(meths, "    ")}\n  ])"
end
puts sentries.join(",\n")

puts "]\n\n/-- Known constants in modeled namespaces; absence is a gate, not NameError. -/"
puts "def crubyNamespaceConstants : List (String × List String) := ["
puts FOLD.map { |name, mods|
  names = mods.first.constants(false) - %i[FOLD NAME_LINES MAIN_SINGLETON]
  "  (#{name.inspect}, [#{names.map(&:to_s).sort.map(&:inspect).join(', ')}])"
}.join(",\n")

puts <<~MID
  ]

  /-- Constants a require may define, curated separately from the oracle's
      already-loaded constants. Preserve the L109 fidelity gate on regeneration. -/
  def crubyStdlibConstants : List String := [
    "YAML", "Date", "DateTime", "OpenSSL", "Digest",
    "Tempfile", "FileUtils", "Shellwords", "StringIO", "Timeout", "Socket",
    "OptionParser", "Open3", "SecureRandom", "Etc", "Zlib", "Base64", "CSV",
    "Logger", "Delegator", "SimpleDelegator", "Singleton", "Observable"
  ]

  /-- Toplevel constants CRuby defines (Object.constants): a constant-lookup
      miss on one of these is "unmodeled", not NameError. -/
  def crubyToplevelConstants : List String := [
MID
puts NAME_LINES.call(
  (Object.constants - %i[FOLD NAME_LINES MAIN_SINGLETON]).map(&:to_s).sort, "  "
)
puts "]"

# Capture each feature in isolation: the core tables above must describe the
# process before optional libraries have been required.
features = %w[forwardable json uri sorbet-runtime].to_h do |feature|
  bytes = IO.popen([RbConfig.ruby, File.join(__dir__, "cruby_feature_names.rb"), feature], &:read)
  abort "feature inventory failed: #{feature}" unless $?.success?
  [feature, Marshal.load(bytes)]
end
puts "\n/-- Names introduced by modeled requires; consulted only after a load attempt. -/"
puts "def crubyFeatureRoots : List (String × List String) := ["
puts features.map { |feature, (roots, _)| "  (#{feature.inspect}, [#{roots.map(&:inspect).join(', ')}])" }.join(",\n")
puts "]"
%w[Methods SingletonMethods Constants].each_with_index do |kind, i|
  puts "\ndef crubyFeature#{kind} : List (String × List String) := ["
  namespaces = features.values.flat_map { |_, mods| mods.to_a }.to_h.sort
  puts namespaces.map { |name, values| "  (#{name.inspect}, [#{values[i].map(&:inspect).join(', ')}])" }.join(",\n")
  puts "]"
end
puts <<~'FOOTER'

  def crubyClassDefines (className mname : String) : Bool :=
    match crubyMethodNames.find? (·.1 == className) with
    | some (_, names) => names.contains mname
    | none => false

  def crubySingletonDefines (className mname : String) : Bool :=
    match crubySingletonNames.find? (·.1 == className) with
    | some (_, names) => names.contains mname
    | none => false

  end RubyCore
FOOTER
