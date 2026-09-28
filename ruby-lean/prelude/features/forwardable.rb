# frozen_string_literal: true

# ─── Forwardable ────────────────────────────────────────────────────────────
#
# `def_delegator :@list, :size` installs a `size` that forwards to `@list.size`.
# Like `Struct`, it is a metaprogramming pattern rather than a library: the whole
# module is `define_method` over a receiver expression, so it costs prelude Ruby
# and no Lean rules. `pkg_version.rb` delegates six methods to its `version`.
#
# The accessor may be an ivar (`:@list`) or a method (`:inner`), which is the one
# case worth being careful about — `instance_variable_get` for the former,
# `send` for the latter [V].
module Forwardable
  def def_delegator(accessor, method, ali = method)
    acc = accessor.to_s
    meth = method.to_sym
    ivar = acc.start_with?("@")
    define_method(ali.to_sym) do |*args, **kw, &blk|
      target = ivar ? instance_variable_get(acc) : send(acc)
      kw.empty? ? target.send(meth, *args, &blk) : target.send(meth, *args, **kw, &blk)
    end
    nil
  end

  def def_delegators(accessor, *methods)
    methods.each { |mm| def_delegator(accessor, mm) }
    nil
  end

  # The `_delegator`-less spellings are the documented aliases.
  def delegate(hash)
    hash.each do |methods, accessor|
      Array(methods).each { |mm| def_delegator(accessor, mm) }
    end
    nil
  end
end
