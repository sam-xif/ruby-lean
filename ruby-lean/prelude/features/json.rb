# frozen_string_literal: true

# ─── JSON — generation only ─────────────────────────────────────────────────
#
# `version_spec.rb` asserts `Version#to_json`, which Homebrew gets from the json
# library. Generation is a pure fold over the value; **parsing is not modeled**
# and `JSON.parse` gates, because the slice never parses (its OSV records arrive
# as already-decoded Hashes in the specs).
module JSON
  def self.generate(obj) = obj.__to_json

  def self.dump(obj) = obj.__to_json

  def self.parse(*args, **kw)
    __unsupported__("JSON.parse (only generation is modeled)")
  end
end

class Object
  # `#<Object:0x…>`-style default: the json library emits the `to_s` for an
  # object it does not know, as a JSON string.
  def __to_json = to_s.__to_json
end

class NilClass
  def __to_json = "null"
end

class TrueClass
  def __to_json = "true"
end

class FalseClass
  def __to_json = "false"
end

class Integer
  def __to_json = to_s
end

class Float
  def __to_json = to_s
end

class Symbol
  def __to_json = to_s.__to_json
end

class String
  # Only the escapes JSON requires: quote, backslash, and the C0 controls. `/`
  # is **not** escaped [V].
  def __to_json
    out = "\""
    each_char do |c|
      out += if c == "\"" then "\\\""
             elsif c == "\\" then "\\\\"
             elsif c == "\n" then "\\n"
             elsif c == "\t" then "\\t"
             elsif c == "\r" then "\\r"
             elsif c.ord < 32 then "\\u" + format("%04x", c.ord)
             else c
             end
    end
    out + "\""
  end
end

class Array
  def __to_json = "[" + map { |e| e.__to_json }.join(",") + "]"
end

class Hash
  def __to_json
    "{" + map { |k, v| k.to_s.__to_json + ":" + v.__to_json }.join(",") + "}"
  end
end


module JSON
  module Ext
    module Generator
      module GeneratorMethods
        module Object
          def to_json(*args) = __to_json
        end
        module Array
          def to_json(*args) = __to_json
        end
        module Hash
          def to_json(*args) = __to_json
        end
        module String
          def to_json(*args) = __to_json
        end
        module Float
          def to_json(*args) = __to_json
        end
        module Integer
          def to_json(*args) = __to_json
        end
        module TrueClass
          def to_json(*args) = __to_json
        end
        module FalseClass
          def to_json(*args) = __to_json
        end
        module NilClass
          def to_json(*args) = __to_json
        end
      end
    end
  end
end

class Object
  include JSON::Ext::Generator::GeneratorMethods::Object
end
class Array
  include JSON::Ext::Generator::GeneratorMethods::Array
end
class Hash
  include JSON::Ext::Generator::GeneratorMethods::Hash
end
class String
  include JSON::Ext::Generator::GeneratorMethods::String
end
class Float
  include JSON::Ext::Generator::GeneratorMethods::Float
end
class Integer
  include JSON::Ext::Generator::GeneratorMethods::Integer
end
class TrueClass
  include JSON::Ext::Generator::GeneratorMethods::TrueClass
end
class FalseClass
  include JSON::Ext::Generator::GeneratorMethods::FalseClass
end
class NilClass
  include JSON::Ext::Generator::GeneratorMethods::NilClass
end
