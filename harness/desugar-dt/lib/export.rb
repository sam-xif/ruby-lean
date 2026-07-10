# frozen_string_literal: true

require "json"

# Serialize a RubyCore S-expression to JSON for out-of-process consumers — the
# Lean model (`ruby/lean/`) is the first. The interface is versioned so either
# side can reject a mismatch (lean-model-sketch.md §2.1, §5).
#
# Encoding: an S-expr node `[:head, ...]` becomes a JSON array whose first
# element is the head as a string; Symbols anywhere (heads, var kinds, rescue
# target kinds) become strings; nil becomes null; Integer/Float/String payloads
# pass through. Decoding is positional per head, so string-vs-symbol ambiguity
# is harmless.
module Export
  VERSION = 1

  module_function

  # Full export document: { "v": 1, "ast": <node> } as a JSON string.
  def json(core)
    JSON.generate({ "v" => VERSION, "ast" => jsonable(core) })
  end

  def jsonable(x)
    case x
    when Symbol then x.to_s
    when Array  then x.map { |e| jsonable(e) }
    when nil, Integer, String then x
    when Float
      raise ArgumentError, "non-finite Float in RubyCore: #{x}" unless x.finite?
      x
    else
      raise ArgumentError, "unexpected value in RubyCore S-expr: #{x.inspect}"
    end
  end
end
