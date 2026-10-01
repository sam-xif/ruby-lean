# typed: strict
# frozen_string_literal: true

# Sorbet 0.6.13405 accepts this file with "No errors!", but CRuby raises
# NoMethodError: Ruby makes initialize_copy (and initialize_dup,
# initialize_clone, respond_to_missing?) private as soon as they are defined,
# whatever visibility the source implies. Sorbet types the explicit call below
# as an ordinary public call returning Integer.
require "sorbet-runtime"

class Version
  extend T::Sig

  sig { params(major: Integer).void }
  def initialize(major)
    @major = T.let(major, Integer)
  end

  sig { returns(Integer) }
  attr_reader :major

  # Looks public; CRuby privatizes it on definition.
  sig { params(other: Version).returns(Integer) }
  def initialize_copy(other)
    @major = other.major
    @major
  end
end

a = Version.new(1)
b = Version.new(2)
copied = T.let(b.initialize_copy(a), Integer) # Sorbet: Integer. CRuby: NoMethodError.
puts copied + 1
