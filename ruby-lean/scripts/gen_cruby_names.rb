#!/usr/bin/env ruby
# frozen_string_literal: true

require "rbconfig"

# Pin the oracle's startup load state. CRuby loads its default gems (rubygems,
# did_you_mean, error_highlight, ...) unless started with --disable-gems, and
# `-r` in RUBYOPT loads whatever the caller injected; both change the tables
# this script snapshots. Re-exec once with a canonical startup — no RUBYOPT and
# no --disable-gems — so `make gen` and `make gen-check` agree on every machine.
# `RUBY_LEAN_GEN_PINNED` stops the re-exec loop when --disable-gems came from
# the command line rather than RUBYOPT.
if ENV["RUBY_LEAN_GEN_PINNED"] != "1" &&
   (ENV["RUBYOPT"].to_s != "" || !defined?(Gem::Specification))
  exec({ "RUBYOPT" => nil, "RUBY_LEAN_GEN_PINNED" => "1" }, RbConfig.ruby, __FILE__, *ARGV)
end

# Regenerate RubyCore/Generated/CRubyNames.lean from the pinned CRuby oracle:
#
#   "$(brew --prefix ruby)/bin/ruby" scripts/gen_cruby_names.rb > RubyCore/Generated/CRubyNames.lean
#
# Emits, for each bootstrap class of the L0 Lean model, the method names
# CRuby defines directly on it (instance + private instance), folding in the
# modules the L0 ancestor chain omits (Kernel→Object, Comparable/Numeric→
# numerics/strings/symbols, Enumerable→Array/Hash), plus Object.constants.
# The Lean model uses these for dispatch fidelity (shadow detection and
# genuine-NoMethodError classification), not behavior.
#
# `--native-instance-names PATH` also writes the checker's projection of the
# same snapshot: the union of every per-class list in `crubyMethodNames`. The
# checker cannot import the model, so it keeps that copy; deriving both from one
# oracle run is what keeps them from drifting (issue #55).

native_instance_path = nil
if (flag = ARGV.index("--native-instance-names"))
  native_instance_path = ARGV.fetch(flag + 1) do
    abort "--native-instance-names requires a path"
  end
end

# Classes the model does not boot as core classes, but whose **class-side**
# surface dispatch must know: the virtual filesystem's `File`/`IO`/`Dir` and the
# pure path wrapper `Pathname`. Their singleton tables go into
# `crubySingletonNames`, so a lookup miss can tell a real class method the model
# declines (`File.mtime`, a named Unsupported) from a name that is not Ruby at
# all (`File.zzz`, an ordinary `NoMethodError`). Only the singleton side is
# emitted: their instance surfaces are still declined wholesale.
GUARDED = { "File" => File, "IO" => IO, "Dir" => Dir, "Pathname" => Pathname }.freeze

# Constants that exist only in some builds of the same CRuby release. They are
# left out so that this table is the same on every platform: `Integer::GMP_VERSION`
# is defined only when CRuby was compiled against GMP.
BUILD_DEPENDENT = %i[GMP_VERSION].freeze

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
  "UncaughtThrowError" => [UncaughtThrowError],
  "NotImplementedError" => [NotImplementedError],
  "ScriptError" => [ScriptError]
}.freeze

# Every constant this script defines. They are filtered out of the constant
# tables below: a toplevel constant lands on Object, which is one of the tables.
SCRIPT_CONSTANTS = (%i[FOLD GUARDED BUILD_DEPENDENT NAME_LINES TABLE_ROW MAIN_SINGLETON] +
                    [:SCRIPT_CONSTANTS]).freeze

# A lambda, not a toplevel def — a def here would land on Object and leak
# into the very tables we are snapshotting.
NAME_LINES = lambda do |names, indent|
  names.each_slice(8).map { |sl| indent + sl.map { |s| s.to_s.inspect }.join(", ") }.join(",\n")
end

# One row of a name table, sorted and wrapped.
TABLE_ROW = lambda do |name, meths|
  "  (\"#{name}\", [\n#{NAME_LINES.call(meths.uniq.sort, "    ")}\n  ])"
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
# main's singleton class. Keep them separate from Object's instance methods.
MAIN_SINGLETON = TOPLEVEL_BINDING.receiver.singleton_class
                                 .then { |sc| sc.instance_methods(false) + sc.private_instance_methods(false) }

instance_methods = FOLD.map do |name, mods|
  meths = mods.flat_map { |m| m.instance_methods(false) + m.private_instance_methods(false) }
  [name, meths.uniq.sort]
end

entries = instance_methods.map do |name, meths|
  "  (\"#{name}\", [\n#{NAME_LINES.call(meths, "    ")}\n  ])"
end
puts entries.join(",\n")

puts "]\n\n/-- Methods native to main's singleton class, not all Objects. -/"
puts "def crubyMainSingletonNames : List String := ["
puts NAME_LINES.call(MAIN_SINGLETON.uniq.sort, "  ")
puts "]"

puts <<~MID
  /-- Singleton (class-side) method names each bootstrap class defines in
      CRuby (e.g. Hash.ruby2_keywords_hash, Array.[]), plus the class-side
      surface of the non-bootstrap classes dispatch guards by name (the
      filesystem's `File`/`IO`/`Dir` and `Pathname`): a send to a class object
      resolving past these must gate, and a name absent from them is not Ruby
      and raises a real `NoMethodError`. -/
  def crubySingletonNames : List (String × List String) := [
MID
sentries = FOLD.map do |name, mods|
  TABLE_ROW.call(name, mods.first.singleton_class
    .then { |sc| sc.instance_methods(false) + sc.private_instance_methods(false) })
end
sentries += GUARDED.map do |name, cls|
  TABLE_ROW.call(name, cls.singleton_class
    .then { |sc| sc.instance_methods(false) + sc.private_instance_methods(false) })
end
puts sentries.join(",\n")

puts "]\n\n/-- Known constants in modeled namespaces; absence is a gate, not NameError. -/"
puts "def crubyNamespaceConstants : List (String × List String) := ["
puts FOLD.map { |name, mods|
  names = mods.first.constants(false) - SCRIPT_CONSTANTS - BUILD_DEPENDENT
  "  (#{name.inspect}, [#{names.map(&:to_s).sort.map(&:inspect).join(", ")}])"
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
  (Object.constants - SCRIPT_CONSTANTS).map(&:to_s).sort, "  "
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
puts features.map { |feature, (roots, _)| "  (#{feature.inspect}, [#{roots.map(&:inspect).join(", ")}])" }.join(",\n")
puts "]"
%w[Methods SingletonMethods Constants].each_with_index do |kind, i|
  puts "\ndef crubyFeature#{kind} : List (String × List String) := ["
  namespaces = features.values.flat_map { |_, mods| mods.to_a }.to_h.sort
  puts namespaces.map { |name, values| "  (#{name.inspect}, [#{values[i].map(&:inspect).join(", ")}])" }.join(",\n")
  puts "]"
end
puts <<~FOOTER

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

if native_instance_path
  names = instance_methods.flat_map { |_, meths| meths }.uniq.sort
  oracle = RUBY_DESCRIPTION.split.first(2).join(" ")
  File.write(native_instance_path, [
    "/-",
    "GENERATED from the CRuby oracle (#{oracle}) by `scripts/gen_cruby_names.rb` — do not hand-edit.",
    "Regenerate with `make gen`.",
    "",
    "Instance selector projection of `RubyCore/Generated/CRubyNames.lean`: the union of",
    "every per-class list in `crubyMethodNames`. The checker imports only this data,",
    "never the interpreter; `Books/TypeSoundness/Conformance/Names/NativePrefix.lean`",
    "kernel-checks it against the model.",
    "-/",
    "namespace Checker",
    "",
    "/-- Every CRuby instance-method name the checker must treat as possibly native. -/",
    "def nativeInstanceNames : List String := [",
    NAME_LINES.call(names, "  "),
    "]",
    "",
    "/-- Sufficient for any inherited native prefix; own calls still use their empty prefix.",
    "This deliberately declines inherited native selector names until a narrower prefix guard. -/",
    "def nativeInstanceFreeB (name : String) : Bool := !nativeInstanceNames.contains name",
    "",
    "end Checker"
  ].join("\n") + "\n")
end
