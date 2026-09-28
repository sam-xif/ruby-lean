# frozen_string_literal: true

# ─── T — the sorbet-runtime shim ────────────────────────────────────────────
#
# Sorbet's *runtime* half, modeled the way this project models everything else:
# as ordinary RubyCore code performing heap mutation, not as new Lean rules
# (`../../AGENTS.md` §Sorbet §A.5, §C.2 — "a `sig` is heap
# mutation that replaces a method-table entry with a checking wrapper").
#
# Why it belongs in the model at all: the honest soundness statement for Sorbet
# is the *runtime* three-outcome one (§C.1 option 2), because the static half is
# unsound by design. That statement is only meaningful if the enforcement
# mechanism is inside the semantics — otherwise there is nothing for the theorem
# to quantify over. With the shim here, "sorbet-runtime raised a TypeError at a
# sig boundary" is an ordinary reachable outcome of `stepFn`, so the existing
# `typeStuck` / `invariant_sound` machinery applies to it unchanged.
#
# Fidelity is established the same way as the rest of the prelude: by difftest
# against the real gem over `difftest/corpus/sorbet/`. Error messages therefore
# match sorbet-runtime **byte for byte**, except for the `Caller:`/`Definition:`
# source-location lines, which RubyCore cannot produce (the AST carries no line
# numbers) and which the engine normalizes away on both sides.

module T
  # A runtime type. sorbet-runtime coerces raw types into `T::Types::*` objects
  # with a `valid?` predicate; the shim keeps that shape but flattens the class
  # hierarchy into one tagged object for validity checks and printed labels.
  # This is still a partial model: its helper namespaces and the full reflected
  # type-object hierarchy are not faithful to the upstream gem.
  #
  # `label` carries the modeled error rendering. General type-object
  # to_s/inspect/equality need a separate conformance audit (authoring rule 3).
  class Type
    def initialize(kind, args, label)
      @kind = kind
      @args = args
      @label = label
    end

    def label
      return @label unless @kind == :proc

      # `T.proc` renders its accumulated chain; the gem prints `params()` even
      # when empty (verified: `T.proc.returns(Integer)` names itself
      # `T.proc.params().returns(Integer)`).
      parts = []
      unless @proc_params.nil?
        @proc_params.each { |k, v| parts.push(k.to_s + ": " + T.type_label(v)) }
      end
      tail = if @proc_void
               ".void"
             elsif @proc_returns.nil?
               ".returns(T.untyped)"
             else
               ".returns(" + T.type_label(@proc_returns) + ")"
             end
      "T.proc.params(" + parts.join(", ") + ")" + tail
    end

    # The `T.proc` builder chain. sorbet-runtime's `T.proc` returns a builder
    # that accumulates `.params`/`.returns`/`.void`, and the resulting type's
    # runtime check is only `is_a?(Proc)` — the declared parameter and return
    # types are **erased**, exactly like generic type arguments (§A.6). That
    # erasure is not an approximation here: it is why
    # `difftest/corpus/sorbet/untyped-boundary/003.rb` reaches a TypeError
    # inside typed code with nothing having checked the block's return.
    def params(**kw)
      @proc_params = kw
      self
    end

    def returns(type)
      @proc_returns = type
      self
    end

    def void
      @proc_void = true
      self
    end

    # Is this `T.nilable(X)`? (`T.nilable` builds an `:any` of X and NilClass.)
    def nilable?
      @kind == :any && !@args.nil? && @args.any? { |a| a == NilClass }
    end

    # The label of the non-nil part, for the T::Struct prop-type message.
    def nilable_inner_label
      rest = @args.reject { |a| a == NilClass }
      rest.length == 1 ? T.type_label(rest[0]) : @label
    end

    def valid?(value)
      k = @kind
      return true if k == :untyped
      return value.is_a?(@args[0]) if k == :simple
      if k == :any
        i = 0
        while i < @args.length
          return true if T.__valid?(@args[i], value)
          i += 1
        end
        return false
      end
      if k == :all
        i = 0
        while i < @args.length
          return false unless T.__valid?(@args[i], value)
          i += 1
        end
        return true
      end
      # Generics are ERASED at runtime (§A.6): the check is the top-level class
      # only, never the element types. This is not a shortcut — it is what
      # sorbet-runtime does, and reproducing it is the point (a heterogeneous
      # array walks straight through, `difftest/corpus/sorbet/generics/000.rb`).
      return value.is_a?(@args[0]) if k == :erased_generic
      return value.is_a?(Proc) if k == :proc
      return value.is_a?(Class) if k == :class_of
      # :self_type / :attached_class / :type_parameter — unchecked at runtime
      true
    end
  end

  # A subscriptable type constructor: `T::Array[Integer]`.
  class GenericType
    def initialize(base, label)
      @base = base
      @label = label
    end

    def [](*args)
      parts = []
      i = 0
      while i < args.length
        parts.push(T.type_label(args[i]))
        i += 1
      end
      T::Type.new(:erased_generic, [@base], @label + "[" + parts.join(", ") + "]")
    end
  end

  # ── coercion and rendering ────────────────────────────────────────────────

  def self.__valid?(type, value)
    return type.valid?(value) if type.is_a?(T::Type)
    return value.is_a?(type) if type.is_a?(Module)
    true
  end

  def self.type_label(type)
    return type.label if type.is_a?(T::Type)
    return type.name if type.is_a?(Module)
    type.inspect
  end

  # `T::Utils.string_truncate_middle(s, 30, 30)`: the gem shortens a long value
  # in a type error to `first 27 + "..." + last 30` [V]. Reproduced because the
  # ellipsis is *observable* — a 100-character String in a failing sig prints
  # differently from the String itself.
  def self.__truncate_middle(s)
    return s if s.length <= 60

    s[0...27] + "..." + s[-30..-1]
  end

  # `T::Types::Base#describe_obj`, byte for byte (gem 0.6.13405, `types/base.rb`).
  # Three rules, none of them guessable and all three observable:
  #
  #   * `nil` / `true` / `false` print **no value clause** — "it would be
  #     redundant to print class and value", says the gem;
  #   * an object whose `inspect` is the **default** one prints `with hash N`
  #     rather than the `#<C:0x…>` the gem calls ugly. `N` is `Object#hash`,
  #     which is *per-process seeded* — no implementation has a stable answer
  #     (N38), so the model refuses here rather than inventing one. It used to
  #     answer the `with value` form, which was simply wrong;
  #   * everything else prints `with value <inspect, truncated>`.
  #
  # The class is named by `to_s`, not `name`: for an anonymous class the gem
  # prints `#<Class:0x…>` and `name` is nil, which made `+` raise a *different*
  # TypeError (the L124 rule, one file over). (L127.)
  def self.__describe_obj(value)
    # `equal?`, not `==`: the gem's `case obj when nil, true, false` dispatches on
    # the *literal* (`nil === obj`), never on `obj`. Writing it as `value == true`
    # dispatches `==` on the value instead, which gates the whole program for any
    # receiver whose `==` is an unmodeled builtin — `T.let((1..2), Integer)` came
    # back `unmodeled builtin would shadow: Range#==`. Identity is exact here:
    # nil/true/false are immediates.
    if value.nil? || value.equal?(true) || value.equal?(false)
      return "type " + value.class.to_s
    end

    if value.__default_inspect?
      __unsupported__("sorbet-runtime: a type error naming an object with the " +
                      "default inspect (the gem prints its per-process `hash`)")
    end
    "type " + value.class.to_s + " with value " + T.__truncate_middle(value.inspect)
  end

  # The shared failure path. Message shapes are sorbet-runtime's, verified
  # against the gem (`difftest/corpus/sorbet/`).
  def self.__check!(prefix, type, value)
    return value if T.__valid?(type, value)
    raise TypeError, prefix + ": Expected type " + T.type_label(type) +
                     ", got " + T.__describe_obj(value)
  end

  # ── the assertion family (§A.3) ───────────────────────────────────────────
  # The static/runtime split is the whole soundness architecture in one table:
  # `T.unsafe` is the ONE form with no runtime check; every other form that is
  # static-unsound is at least runtime-checked. That asymmetry is reproduced
  # exactly here.

  def self.let(value, type)
    __check!("T.let", type, value)
  end

  def self.cast(value, type)
    __check!("T.cast", type, value)
  end

  def self.assert_type!(value, type)
    __check!("T.assert_type!", type, value)
  end

  def self.must(value)
    raise TypeError, "Passed `nil` into T.must" if value.nil?
    value
  end

  # No runtime check at all — the escape hatch, faithfully unchecked.
  def self.unsafe(value)
    value
  end

  # `T.bind(self, X)`: trusted statically, checked at runtime like T.cast.
  def self.bind(value, type)
    __check!("T.bind", type, value)
  end

  # A static-only tool: at runtime it is the identity.
  def self.reveal_type(value)
    value
  end

  # Exhaustiveness. Statically proves all cases are handled; reaching it at
  # runtime means the static proof did not apply, and the gem raises.
  def self.absurd(value)
    raise TypeError, "Control flow reached T.absurd."
  end

  # ── type constructors (§A.1) ──────────────────────────────────────────────

  def self.untyped
    T::Type.new(:untyped, [], "T.untyped")
  end

  def self.noreturn
    T::Type.new(:untyped, [], "T.noreturn")
  end

  def self.anything
    T::Type.new(:untyped, [], "T.anything")
  end

  def self.self_type
    T::Type.new(:self_type, [], "T.self_type")
  end

  def self.attached_class
    T::Type.new(:attached_class, [], "T.attached_class")
  end

  def self.type_parameter(name)
    T::Type.new(:type_parameter, [], "T.type_parameter(:" + name.to_s + ")")
  end

  def self.class_of(klass)
    T::Type.new(:class_of, [klass], "T.class_of(" + T.type_label(klass) + ")")
  end

  def self.any(*types)
    T::Type.new(:any, types, "T.any(" + T.__labels(types) + ")")
  end

  def self.all(*types)
    T::Type.new(:all, types, "T.all(" + T.__labels(types) + ")")
  end

  # `T.nilable(x)` is *literally* `T.any(NilClass, x)` [D: /docs/union-types],
  # but it prints under its own name.
  def self.nilable(type)
    T::Type.new(:any, [NilClass, type], "T.nilable(" + T.type_label(type) + ")")
  end

  def self.proc
    T::Type.new(:proc, [], "T.proc")
  end

  def self.type_alias(&blk)
    yield
  end

  def self.__labels(types)
    parts = []
    i = 0
    while i < types.length
      parts.push(T.type_label(types[i]))
      i += 1
    end
    parts.join(", ")
  end

  # ── the sig DSL and its runtime enforcement (§A.5) ────────────────────────

  # Records what a `sig { … }` block declared. The block is `instance_eval`ed
  # against one of these, so every DSL method returns self to keep the chain
  # going.
  class Decl
    def initialize
      @params = nil
      @returns = nil
      @void = false
      @checked = :always
    end

    def param_types
      @params
    end

    def return_type
      @returns
    end

    def void?
      @void
    end

    def checked_level
      @checked
    end

    def params(**kw)
      @params = kw
      self
    end

    def returns(type)
      @returns = type
      self
    end

    def void
      @void = true
      self
    end

    def checked(level)
      @checked = level
      self
    end

    # Declarations with no runtime effect. They exist so a real-world sig
    # parses; the static half is Sorbet's business, not the model's.
    def on_failure(*args)
      self
    end

    def type_parameters(*args)
      self
    end

    def abstract
      self
    end

    def overridable
      self
    end

    def override(**kw)
      self
    end

    def final
      self
    end

    def bind(type)
      self
    end
  end

  # `extend T::Sig` is what puts `sig` in a class body. Enforcement rides on
  # `Module#method_added`: `sig` records a pending declaration and the hook
  # wraps the method defined immediately after — the same mechanism the real
  # gem uses, which is why the model had to grow the hook (L77).
  module Sig
    def sig(&blk)
      # In a class/module body `self` is the definee and `T::Sig#method_added`
      # (an instance method of the extended module, so it sits on the class
      # object's singleton chain) is already the hook. At **toplevel** `self` is
      # `main`, not a Module: the `def` that follows lands on Object, whose
      # `method_added` must therefore be installed explicitly. The real gem does
      # the same thing — `sig` installs hooks on the definee rather than
      # assuming they are there.
      if self.is_a?(Module)
        @__t_pending_sig = blk
      else
        T.__toplevel_sig(blk)
      end
      nil
    end

    def method_added(name)
      T.__hook(self, name)
    end
  end

  def self.__toplevel_sig(blk)
    Object.instance_variable_set(:@__t_pending_sig, blk)
    return nil if @__toplevel_hook_installed
    @__toplevel_hook_installed = true
    # A *singleton* method on Object, so it resolves ahead of CRuby's
    # `Module#method_added` no-op (a plain Object instance method would be
    # shadowed by it — see the `.def'` rule in Interp.lean).
    Object.define_singleton_method(:method_added) do |name|
      T.__hook(Object, name)
    end
    nil
  end

  # The hook body, shared by the class-body and toplevel paths.
  def self.__hook(mod, name)
    blk = mod.instance_variable_get(:@__t_pending_sig)
    return nil if blk.nil?
    mod.instance_variable_set(:@__t_pending_sig, nil)
    # Re-entrancy guard: installing the wrapper defines a method, and CRuby
    # fires `method_added` for `define_method` too. Without this a sig would
    # wrap its own wrapper forever.
    return nil if mod.instance_variable_get(:@__t_wrapping)
    mod.instance_variable_set(:@__t_wrapping, true)
    T.__wrap(mod, name, blk)
    mod.instance_variable_set(:@__t_wrapping, false)
    nil
  end

  # Install the checking wrapper: alias the original aside, then define a
  # forwarding method that validates arguments, calls through, and validates the
  # return. This IS the heap mutation of §C.2 — a method-table entry replaced by
  # a checking one.
  # The sig block is evaluated **lazily, once, on the first call** of the method
  # it governs — not at `def` time. That is what the real gem does, and it is
  # not a detail: a sig may name a constant that is not defined yet when the
  # class body runs (`utils/output.rb` has `T.nilable(Time)` in a sig, with
  # `Time` supplied later by the boot path), and evaluating eagerly turns that
  # into a load-time NameError the real program never sees. The `cache` array is
  # captured by the wrapper's closure, so the memo needs no `object_id` and no
  # global table.
  #
  # Consequence of laziness, recorded rather than hidden: `.checked(:never)`
  # can no longer skip *installing* the wrapper (deciding that would mean
  # evaluating the block eagerly), so the wrapper is always installed and calls
  # straight through instead. The escape hatch still skips every check; what
  # changes is only that the frame is present, which is the same reflective
  # visibility the gradual-guarantee probe already records as a violation (N33).
  def self.__wrap(mod, name, blk)
    # The hidden alias must be **unique per module**, not just per method name.
    # With a flat `__t_unchecked_initialize`, a subclass's alias shadows its
    # parent's, so the parent wrapper's `send(hidden, …)` dispatches back into
    # the *subclass's* original body — which is how `Version::NullToken`'s
    # zero-argument `initialize` ended up receiving `Token#initialize`'s one
    # argument ("wrong number of arguments (given 1, expected 0)"). The bug was
    # latent until L107 stopped gating sigs with keyword parameters.
    hidden = "__t_u_" + (mod.name.nil? ? "anon" : mod.name.gsub("::", "_")) +
             "__" + name.to_s
    cache = []
    mod.send(:alias_method, hidden, name)
    mod.send(:define_method, name) do |*args, **kw, &b|
      if cache.empty?
        d = T::Decl.new
        d.instance_eval(&blk)
        cache.push(d)
      end
      decl = cache[0]
      if decl.checked_level == :never
        kw.empty? ? send(hidden, *args, &b) : send(hidden, *args, **kw, &b)
      else
        T.__check_params_kw(decl, args, kw)
        result = kw.empty? ? send(hidden, *args, &b) : send(hidden, *args, **kw, &b)
        T.__check_return(decl, result)
      end
    end
    nil
  end

  # Positional-or-keyword matching (L107). Sorbet requires a sig to list the
  # method's parameters in order, so the i-th *positional* declared name governs
  # the i-th argument; a declared name that appears as a **key in `kw`** is a
  # keyword parameter and is checked against that value instead. The shim has no
  # `instance_method(…).parameters` to consult, but it does not need one: the
  # call itself says which names arrived as keywords. A declared name that is
  # neither is an optional parameter the caller omitted, and there is nothing to
  # check. This replaces the old rule, which gated the whole sig as soon as it
  # declared more names than there were positional arguments — 186 of the
  # Homebrew-slice corpus's programs.
  def self.__check_params_kw(decl, args, kw)
    types = decl.param_types
    return nil if types.nil?
    i = 0
    types.keys.each do |key|
      if kw.key?(key)
        T.__check!("Parameter '" + key.to_s + "'", types[key], kw[key])
      elsif i < args.length
        T.__check!("Parameter '" + key.to_s + "'", types[key], args[i])
        i += 1
      end
    end
    nil
  end

  def self.__check_params(decl, args)
    types = decl.param_types
    return nil if types.nil?
    names = types.keys
    return __unsupported__("sorbet-runtime: sig with more params than arguments (keyword params?)") if names.length > args.length
    i = 0
    while i < names.length
      key = names[i]
      __check!("Parameter '" + key.to_s + "'", types[key], args[i])
      i += 1
    end
    nil
  end

  def self.__check_return(decl, result)
    # `.void` discards the real return value and yields sorbet's VOID sentinel,
    # which IS observable (`p` prints it), so the shim reproduces it.
    return T::Private::Types::Void::VOID if decl.void?
    rt = decl.return_type
    return result if rt.nil?
    __check!("Return value", rt, result)
  end

  module Private
    module Types
      module Void
        module VOID
        end
      end
    end
  end
end

# `extend T::Helpers` is the other half of the annotation surface (the `sig`
# half is `T::Sig`). Everything it installs is a *declaration*: `abstract!`
# and `interface!` tell the static checker that instantiating or calling is a
# type error, `sealed!`/`final!` restrict subclassing, `requires_ancestor`
# constrains where a module may be mixed in — none of them changes what a
# correct program does at runtime.
#
# sorbet-runtime does add one runtime behaviour to `abstract!`: calling an
# unimplemented abstract method raises `NotImplementedError`. That is
# reproduced below rather than dropped, because it is a reachable outcome and
# dropping it would make an abstract call silently return nil.
#
# `mixes_in_class_methods(M)` is the one with real semantics — the includer
# gets `extend M` — so it is implemented rather than declared.
module T
  module Helpers
    # `abstract!` / `interface!` are mostly declarations, but they have one
    # runtime effect and the slice's specs test it: the abstract class itself
    # cannot be instantiated [V] —
    # `RuntimeError: A is declared as abstract; it cannot be instantiated`.
    # Subclasses can, so the guard compares against the declaring class and the
    # inherited path allocates and initializes directly (rather than `super`,
    # which from a `define_singleton_method` body would have to resolve through
    # the eigenclass chain).
    def abstract!
      @__t_abstract = true
      cls = self
      define_singleton_method(:new) do |*a, **kw, &b|
        if equal?(cls)
          raise RuntimeError, cls.name + " is declared as abstract; it cannot be instantiated"
        end
        obj = allocate
        obj.send(:initialize, *a, **kw, &b)
        obj
      end
      nil
    end

    def interface!
      abstract!
    end

    def sealed!
      nil
    end

    def final!
      nil
    end

    # Takes a block naming the required ancestor; purely static.
    def requires_ancestor(&blk)
      nil
    end

    def mixes_in_class_methods(*mods)
      @__t_class_methods = mods
      nil
    end

    def included(base)
      mods = @__t_class_methods
      base.extend(mods[0]) if !mods.nil? && mods.length == 1
      nil
    end
  end
end

# Subscriptable generic constructors and the Boolean alias. Assigned at toplevel
# (not inside `module T`) so `Array`/`Hash` resolve to the real classes rather
# than to the constants being defined.
T::Array = T::GenericType.new(Array, "T::Array")
T::Hash = T::GenericType.new(Hash, "T::Hash")
T::Range = T::GenericType.new(Range, "T::Range")
T::Enumerable = T::GenericType.new(Enumerable, "T::Enumerable")
T::Boolean = T::Type.new(:any, [TrueClass, FalseClass], "T::Boolean")

# `T::Struct` / `T::Enum` are **structural**, not annotations: they define a
# class hierarchy and generate methods, so a program using them cannot be
# understood by ignoring them. Until they are modeled they gate at first use —
# an honest Unsupported rather than a NameError that would read as a wrong
# answer (the difftest engine's one unforgivable verdict).
# `T::Struct` — a typed record. Like `Struct` (L105) this is a metaprogramming
# pattern rather than a core class: `const`/`prop` are class macros that record a
# property and define its reader, and `initialize` is generated from the record.
# It could not live in the prelude before L103, because a `T::Struct` needs its
# own `inspect`.
#
# Two behaviours that a plausible implementation gets wrong, both verified
# against the gem [V]:
#   * `T::Struct` does **not** define `==` — two structs with equal fields are
#     *not* equal, because equality stays identity (inherited from Object).
#   * `inspect` lists the props **alphabetically**, while `serialize` lists them
#     in declaration order and **omits nil**.
class T::Struct
  def self.__own_props
    @__props = [] if @__props.nil?
    @__props
  end

  # Props are inherited, parents first.
  def self.__all_props
    sup = superclass
    base = (!sup.nil? && sup.respond_to?(:__all_props)) ? sup.__all_props : []
    base + __own_props
  end

  # The gem exposes `props` as a Hash keyed by prop name.
  def self.props
    h = {}
    __all_props.each { |pp| h[pp[0]] = { type: pp[1] } }
    h
  end

  def self.const(name, type, default: :__t_none, factory: nil)
    __define_prop(name, type, false, default)
  end

  def self.prop(name, type, default: :__t_none, factory: nil)
    __define_prop(name, type, true, default)
  end

  def self.__define_prop(name, type, mutable, default)
    nm = name.to_sym
    __own_props.push([nm, type, mutable, default])
    ivar = "@" + nm.to_s
    define_method(nm) { instance_variable_get(ivar) }
    if mutable
      cls = self
      define_method(nm.to_s + "=") do |v|
        T.__struct_check(cls, nm, type, v)
        instance_variable_set(ivar, v)
      end
    end
    nil
  end

  def initialize(**kw)
    ps = self.class.__all_props
    known = ps.map { |pp| pp[0] }
    extra = kw.keys.reject { |k| known.include?(k) }
    unless extra.empty?
      raise ArgumentError, self.class.name + ": Unrecognized properties: " +
                           extra.map { |k| k.to_s }.join(", ")
    end
    ps.each do |pp|
      nm = pp[0]
      type = pp[1]
      dflt = pp[3]
      if kw.key?(nm)
        v = kw[nm]
        T.__struct_check(self.class, nm, type, v)
      elsif dflt != :__t_none
        v = dflt
      elsif T.__struct_nilable?(type)
        v = nil
      else
        raise ArgumentError, "Missing required prop `" + nm.to_s +
                             "` for class `" + self.class.name + "`"
      end
      instance_variable_set("@" + nm.to_s, v)
    end
    nil
  end

  def inspect
    ps = self.class.__all_props.map { |pp| pp[0].to_s }.sort
    "<" + self.class.name + " " +
      ps.map { |n| n + "=" + send(n).inspect }.join(" ") + ">"
  end

  def to_s
    inspect
  end

  def serialize(strict = true)
    h = {}
    self.class.__all_props.each do |pp|
      v = send(pp[0])
      h[pp[0].to_s] = v unless v.nil?
    end
    h
  end
end

module T
  # A prop typed `T.nilable(X)` with no default starts as nil [V].
  def self.__struct_nilable?(type)
    return false unless type.is_a?(T::Type)
    type.nilable?
  end

  # The gem reports the *non-nil* part of a nilable prop's type in this message
  # ("need a String", not "need a T.nilable(String)") [V]. The `Caller:` line the
  # gem appends is a source location RubyCore cannot produce; the difftest engine
  # normalizes it away on both sides (see the shim header).
  def self.__struct_check(cls, name, type, value)
    return value if T.__valid?(type, value)
    want = (type.is_a?(T::Type) && type.nilable?) ? type.nilable_inner_label : T.type_label(type)
    # A *different* rule from `__describe_obj` above, and checked separately
    # against the gem: this path prints the plain `inspect` — no truncation, no
    # hash substitution, addresses and all (the difftest engine normalizes those)
    # — and names the class with `to_s`, so an anonymous one is `#<Class:0x…>`
    # rather than the nil that `name` answers (L127).
    raise TypeError, "Parameter '" + name.to_s + "': Can't set " + cls.to_s + "." +
                     name.to_s + " to " + value.inspect + " (instance of " +
                     value.class.to_s + ") - need a " + want
  end
end

class T::Enum
  def self.enums(*args)
    __unsupported__("T::Enum")
  end
end
