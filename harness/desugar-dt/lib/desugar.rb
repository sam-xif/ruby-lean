# frozen_string_literal: true

require "prism"
require_relative "rubycore"
require_relative "linearize"

# desugar : Prism AST -> RubyCore (tagged S-expressions).
#
# Each interesting rewrite records a rule name in `@coverage` (artifact 06 §5). Any Prism
# node outside the modeled fragment raises Desugar::Unsupported, which the driver turns
# into an OUT-OF-FRAGMENT skip.
class Desugar
  class Unsupported < StandardError; end

  # Every rule name `fire` can emit — used by the driver to report coverage gaps.
  RULES = %i[
    seq int flt str sym true false nil self var vasgn const casgn send block def array hash
    splat if while return break next and->if or->if unless->if until->while
    or-write and-write op-write range->send rational->send imaginary->send interp massign
    class module sclass defs begin retry super zsuper rescue-mod->begin attr-index-write
    yield lambda->send block-capture blockpass
    opt-param kw-param kwrest-param kwargs case->if defined cpath cpath-asgn
    redo undef alias for regex isym massign-to_ary fwd-arg fwd-param when-splat
    index-opwrite attr-opwrite numbered-params dowhile destructure-param
    vcall implicit safe-nav
  ].freeze

  attr_reader :coverage

  # DESUGAR_BUG=1 switches &&/|| to the *naive* double-evaluating form, purely to
  # demonstrate that the evaluation-order trace catches it (implementation-choices.md C4).
  def initialize(inject_bug: ENV["DESUGAR_BUG"] == "1")
    @gensym = 0
    @coverage = []
    @inject_bug = inject_bug
    @fn_depth = 0        # >0 while inside a def body (gates top-level `return`)
  end

  # Convenience: parse source, desugar the whole program, then linearize (hoist
  # unconditional jumps out of operand position) so the result is renderable.
  def self.program(src, **opts)
    d = new(**opts)
    result = Prism.parse(src)
    raise Unsupported, "parse error" unless result.success?

    [Linearize.run(d.node(result.value)), d.coverage]
  end

  def fire(rule)
    @coverage << rule unless @coverage.include?(rule)
  end

  def fresh
    "__dt_t#{@gensym += 1}"
  end

  # Dispatch on Prism node type.
  def node(n)
    case n.type
    when :program_node            then stmts(n.statements)
    when :statements_node         then stmts(n)
    when :parentheses_node        then n.body ? stmts(n.body) : [:nil]
    when :integer_node            then fire(:int);  [:int, n.value]
    when :float_node              then fire(:flt);  float_lit(n.value)
    when :range_node              then desugar_range(n)
    when :rational_node           then desugar_rational(n)
    when :imaginary_node          then desugar_imaginary(n)
    when :string_node             then fire(:str);  [:str, n.unescaped]
    when :symbol_node             then fire(:sym);  [:sym, n.unescaped]
    when :true_node               then fire(:true);  [:true]
    when :false_node              then fire(:false); [:false]
    when :nil_node                then fire(:nil);   [:nil]
    when :self_node               then fire(:self);  [:self]
    when :local_variable_read_node    then fire(:var);   [:var, :local, n.name.to_s]
    when :local_variable_write_node   then fire(:vasgn); [:vasgn, :local, n.name.to_s, node(n.value)]
    when :instance_variable_read_node  then fire(:var);   [:var, :ivar, n.name.to_s]
    when :instance_variable_write_node then fire(:vasgn); [:vasgn, :ivar, n.name.to_s, node(n.value)]
    when :class_variable_read_node     then fire(:var);   [:var, :cvar, n.name.to_s]
    when :class_variable_write_node    then fire(:vasgn); [:vasgn, :cvar, n.name.to_s, node(n.value)]
    when :global_variable_read_node    then fire(:var);   [:var, :gvar, n.name.to_s]
    when :global_variable_write_node   then fire(:vasgn); [:vasgn, :gvar, n.name.to_s, node(n.value)]
    when :constant_read_node           then fire(:const); [:const, n.name.to_s]
    when :constant_write_node          then fire(:casgn); [:casgn, n.name.to_s, node(n.value)]
    when :call_node               then call(n)
    when :and_node                then andor(n, and_kind: true)
    when :or_node                 then andor(n, and_kind: false)
    when :if_node                 then desugar_if(n)
    when :unless_node             then desugar_unless(n)
    when :while_node              then desugar_while(n, negate: false)
    when :def_node                then desugar_def(n)
    when :until_node              then desugar_while(n, negate: true)
    when :local_variable_or_write_node     then logic_write(n, :local, or_kind: true)
    when :local_variable_and_write_node    then logic_write(n, :local, or_kind: false)
    when :instance_variable_or_write_node  then logic_write(n, :ivar, or_kind: true)
    when :instance_variable_and_write_node then logic_write(n, :ivar, or_kind: false)
    when :global_variable_or_write_node    then logic_write(n, :gvar, or_kind: true)
    when :global_variable_and_write_node   then logic_write(n, :gvar, or_kind: false)
    when :local_variable_operator_write_node    then op_write(n, :local)
    when :instance_variable_operator_write_node  then op_write(n, :ivar)
    when :class_variable_operator_write_node     then op_write(n, :cvar)
    when :global_variable_operator_write_node    then op_write(n, :gvar)
    when :constant_operator_write_node           then op_write(n, :const)
    when :interpolated_string_node then interp(n)
    when :array_node              then desugar_array(n)
    when :hash_node               then desugar_hash(n)
    when :return_node             then desugar_jump(n, :return)
    when :break_node              then desugar_jump(n, :break)
    when :next_node               then desugar_jump(n, :next)
    when :multi_write_node        then desugar_massign(n)
    when :class_node              then desugar_class(n)
    when :module_node             then desugar_module(n)
    when :singleton_class_node    then desugar_sclass(n)
    when :begin_node              then desugar_begin(n)
    when :rescue_modifier_node    then desugar_rescue_modifier(n)
    when :retry_node              then fire(:retry); [:retry]
    when :super_node              then desugar_super(n)
    when :forwarding_super_node   then desugar_zsuper(n)
    when :yield_node              then desugar_yield(n)
    when :lambda_node             then desugar_lambda(n)
    when :case_node               then desugar_case(n)
    when :defined_node            then desugar_defined(n)
    when :constant_path_node      then desugar_cpath(n)
    when :constant_path_write_node then desugar_cpath_write(n)
    when :redo_node               then fire(:redo); [:redo]
    when :undef_node              then desugar_undef(n)
    when :alias_method_node       then desugar_alias(n.new_name, n.old_name)
    when :alias_global_variable_node then desugar_alias(n.new_name, n.old_name)
    when :for_node                then desugar_for(n)
    when :regular_expression_node, :interpolated_regular_expression_node then desugar_regex(n)
    when :interpolated_symbol_node then desugar_isym(n)
    when :index_operator_write_node then desugar_index_write(n, :op)
    when :index_or_write_node       then desugar_index_write(n, :or)
    when :index_and_write_node      then desugar_index_write(n, :and)
    when :call_operator_write_node  then desugar_attr_write(n, :op)
    when :call_or_write_node        then desugar_attr_write(n, :or)
    when :call_and_write_node       then desugar_attr_write(n, :and)
    # Regex match globals — read-only thread-local match state; render back verbatim as
    # gvar reads (`$1`, `$&`). `$~`/`$`'`/etc. already arrive as global_variable_read_node.
    # Ruby 3.1 hash/keyword shorthand `{x:}` / `foo(x:)`. Prism has already resolved the
    # omitted value to the node it stands for (a local read or a self-call), so the
    # desugaring is `x: x` with that resolution — pure sugar. (C32.)
    when :implicit_node           then fire(:implicit); node(n.value)
    when :numbered_reference_read_node then fire(:var); [:var, :gvar, "$#{n.number}"]
    when :back_reference_read_node     then fire(:var); [:var, :gvar, n.name.to_s]
    # Out of scope (documented, self-describing gate reasons):
    when :source_line_node, :source_file_node
      raise Unsupported, "__LINE__/__FILE__ (source-location reflection — changes under re-render)"
    when :x_string_node, :interpolated_x_string_node
      raise Unsupported, "backtick x-string (spawns an external process — out of scope, cf. eval)"
    when :flip_flop_node
      raise Unsupported, "flip-flop operator (stateful per-instance control — deferred)"
    else
      raise Unsupported, "node type :#{n.type}"
    end
  end

  private

  # A `-0.0` literal must not become a bare `[:flt, -0.0]`: the RubyCore JSON export
  # encodes floats as JSON numbers, and JSON/Lean's `JsonNumber` cannot carry a
  # negative zero (mantissa is a signless `Int 0`), so the sign would be lost and
  # `(-0.0).inspect` would wrongly print `0.0`. Emit it as `-@` of `+0.0` instead,
  # which round-trips through the model's (correct) `Float#-@`. (desugar choice C31.)
  def float_lit(v)
    if v == 0.0 && (1.0 / v).negative?
      [:send, [:flt, 0.0], "-@", [], nil]
    else
      [:flt, v]
    end
  end

  def stmts(statements_node)
    return [:nil] if statements_node.nil?
    # A method/block/parens "body" slot may hold a non-StatementsNode (e.g. a BeginNode
    # for `begin/rescue`, or a single expression). Route those through node() so they get
    # a clean Unsupported instead of a NoMethodError on `.body`.
    return node(statements_node) unless statements_node.type == :statements_node

    body = statements_node.body
    return [:nil] if body.empty?
    return node(body.first) if body.length == 1

    fire(:seq)
    [:seq, *body.map { |s| node(s) }]
  end

  def negate(core)
    [:send, core, "!", [], nil]
  end

  # call families that smuggle arbitrary source past the fragment gate. `eval` of a
  # string is explicitly out of scope (artifact 00 §6, PROJECT_PLAN §4); the block forms
  # of *_eval are fine and handled as ordinary sends with a block.
  EVAL_STRINGISH = %w[instance_eval class_eval module_eval].freeze

  def call(n)
    name = n.name.to_s
    if name == "eval"
      raise Unsupported, "eval of string (out of scope, artifact 00 §6)"
    end
    if EVAL_STRINGISH.include?(name) && n.arguments&.arguments&.first&.type == :string_node
      raise Unsupported, "#{name} of string (out of scope, artifact 00 §6)"
    end

    # Assignment-call (`recv[i] = v`, `recv.attr = v`): Prism emits a call_node to `[]=` /
    # `attr=` but marks it with `equal_loc`. Unlike a normal send, the *value* of the
    # expression is the RHS `v`, not the writer method's return. Desugar to preserve both
    # the value and left-to-right single-evaluation (recv, indices, then v).
    return assign_call(n) if n.equal_loc

    # A **vcall** — a bare identifier that is not a local variable (Prism's
    # `variable_call?`: no receiver, no parens, no args, no block). Semantically an
    # implicit-self zero-arg send, but it is emitted as its own head because CRuby's
    # dispatch-*miss* message differs [V]:
    #   `foo`   → NameError: undefined local variable or method 'foo'
    #   `foo()` → NoMethodError: undefined method 'foo'
    # Conflating them forced the model to gate the miss. Additive: ordinary sends and
    # the existing v4 corpus are unchanged.
    if n.variable_call?
      fire(:vcall)
      return [:vcall, name]
    end

    fire(:send)
    recv  = n.receiver ? node(n.receiver) : nil
    args  = n.arguments ? n.arguments.arguments.map { |a| arg_node(a) } : []
    block = call_block(n.block)
    send = [:send, recv, n.name.to_s, args, block]
    n.safe_navigation? ? safe_nav(recv, send) : send
  end

  # `recv&.m(args)` — nil-guarded send (C34). The receiver is evaluated **once**
  # and the arguments are not evaluated at all when it is nil, so the guard has
  # to bind a temp and wrap the whole send, not just test the receiver twice.
  # Not sugar for `recv && recv.m`: `false&.to_s` calls `to_s` [V], because the
  # guard is `nil?`, not truthiness.
  def safe_nav(recv, send)
    fire(:"safe-nav")
    t = fresh
    guarded = send.dup
    guarded[1] = [:var, :local, t]
    [:seq,
     [:vasgn, :local, t, recv],
     [:if, [:send, [:var, :local, t], "nil?", [], nil], [:nil], guarded]]
  end

  # recv.WRITER(idx..., rhs) where the expression value must be `rhs`. We bind rhs to a
  # fresh temp *in its own (last) argument position* — so recv and the index args are still
  # evaluated first, in order, exactly once — then return the temp. No temp is needed for
  # recv/indices: each is evaluated once by the send itself.
  def assign_call(n)
    fire(:"attr-index-write")
    recv = n.receiver ? node(n.receiver) : nil
    all  = n.arguments ? n.arguments.arguments.map { |a| arg_node(a) } : []
    raise Unsupported, "assignment-call without RHS arg" if all.empty?
    *idx, rhs = all
    t = fresh
    [:seq, [:send, recv, n.name.to_s, idx + [[:vasgn, :local, t, rhs]], nil], [:var, :local, t]]
  end

  # An element of an argument list or array literal — may be a splat (`*e`) or a trailing
  # keyword-hash (`a: 1, **h`). A keyword-hash is kept as a `[:kwargs, …]` marker rather
  # than desugared to a positional hash, because Ruby 3 separates keyword args from a
  # positional hash (a positional-hash literal uses braces; the marker renders brace-less).
  def arg_node(a)
    case a.type
    when :splat_node
      fire(:splat)
      [:splat, a.expression ? node(a.expression) : nil]
    when :keyword_hash_node
      kwargs_node(a)
    when :forwarding_arguments_node
      fire(:"fwd-arg")
      [:fwd]                       # `...` — forward the enclosing method's forwarded args
    else
      node(a)
    end
  end

  # foo(a: 1, "b" => 2, **h) — a brace-less keyword hash. elem = [k, v] (assoc) or
  # [:kwsplat, e_or_nil] (`**h` / anonymous `**`). Keys may be non-symbol (`"b" => 2`).
  def kwargs_node(kh)
    fire(:kwargs)
    elems = kh.elements.map do |el|
      case el.type
      when :assoc_node       then [node(el.key), node(el.value)]
      when :assoc_splat_node then [:kwsplat, el.value ? node(el.value) : nil]
      else raise Unsupported, "kwargs elem :#{el.type}"
      end
    end
    [:kwargs, elems]
  end

  # A send/super block slot: either a literal block `{…}`/`do…end` (:block_node) or a
  # block-pass argument `&expr` (:block_argument_node). The two are mutually exclusive in
  # Ruby (both parse into `.block`). A block-pass becomes [:blockpass, expr_or_nil]; the
  # expression is nil for an anonymous `&` (forwarding the enclosing method's `&`).
  def call_block(b)
    return nil if b.nil?
    case b.type
    when :block_node then block_node(b)
    when :block_argument_node
      fire(:blockpass)
      [:blockpass, b.expression ? node(b.expression) : nil]
    else raise Unsupported, "call block type :#{b.type}"
    end
  end

  def block_node(b)
    raise Unsupported, "block type :#{b.type}" unless b.type == :block_node

    params, locals = block_params(b.parameters)
    fire(:block)
    [:block, params, locals, declared_locals(b, params, locals), stmts(b.body)]
  end

  # Ruby decides local scoping **lexically, at parse time**: a name whose first
  # assignment in the text is inside this block is local to the block, even when
  # the enclosing scope assigns it later. Nothing in the runtime heap can recover
  # that — the whole point is that the answer differs from what the heap shows when
  # the block is *called* after the outer assignment — so the front end has to say
  # it. Prism has already computed the set, per scope, as `node.locals`. C35.
  #
  # Kept in its own slot rather than merged into the `|params; locals|` one: the two
  # are identical at runtime (both are names the block frame binds itself) but they
  # differ for `defined?`, which CRuby answers statically — an explicit `|;x|` is
  # "local-variable" before any assignment, an implicit one is nil until the
  # assignment is passed textually. `render.rb` must therefore *not* render these,
  # and the Lean side, which decides `defined?` from the node shape alone (L72),
  # merges the two lists at decode.
  def declared_locals(scope, params, explicit)
    bound = param_names(params) + explicit
    scope.locals.map(&:to_s).reject do |n|
      # `_1`…`_9` are numbered params, which Prism reports as scope locals and
      # which no declaration slot may name (C29 keeps them verbatim).
      bound.include?(n) || n.match?(/\A_[1-9]\z/)
    end
  end

  # Every name the parameter list binds, including through a destructure.
  def param_names(params)
    params.flat_map do |p|
      case p[0]
      when :preq, :popt, :pkey then [p[1]]
      when :prest, :pkwrest, :pblock then p[1] ? [p[1]] : []
      when :pdestr then param_names(p[1])
      else []
      end
    end
  end

  # Positional params + block-local names (`|params; locals|`) from a
  # BlockParametersNode (block or lambda), or [[], []] when absent.
  def block_params(bp)
    return [[], []] if bp.nil?
    # Numbered params (`{ _1 + _2 }`). C29 emitted **no** params, on the reasoning that
    # the body's `_1`… render verbatim and Ruby re-detects them — true for the render
    # round-trip and false for anyone reading the AST: the Lean model bound nothing, so
    # `[1].map { _1 + 1 }` answered `NoMethodError: undefined method '+' for nil`. A
    # silent wrong answer, since the reads desugar to `var local` (Prism knows they are
    # locals), not to a vcall that would have raised honestly. Prism's `maximum` gives
    # the arity, and `_1`…`_max` are exactly the required params Ruby binds — including
    # the auto-splat, which follows from arity ≥ 2 [V]: `[[1,2]].map { _1 }` is
    # `[[1, 2]]` and `[[1,2]].map { _1 + _2 }` is `[3]`. `render.rb` still emits no
    # parameter list, because `|_1|` is a syntax error ("_1 is reserved for numbered
    # parameter") — re-parsing recovers the same synthesized list, so the round-trip
    # stays a fixpoint. C36.
    if bp.type == :numbered_parameters_node
      fire(:"numbered-params")
      return [(1..bp.maximum).map { |i| [:preq, "_#{i}"] }, []]
    end
    raise Unsupported, "block param type :#{bp.type}" unless bp.type == :block_parameters_node
    [build_params(bp.parameters), bp.locals.map { |l| l.name.to_s }]
  end

  # `yield args` — invoke the current method frame's block (artifact 04 §2).
  def desugar_yield(n)
    args = n.arguments ? n.arguments.arguments.map { |a| arg_node(a) } : []
    fire(:yield)
    [:yield, args]
  end

  # `->(params){body}` is a lambda. It is behavior-identical to `lambda { |params|
  # body }`, so we desugar to that send-with-block — no new head, and lambda-ness
  # stays a property the callee (`lambda`) confers on the block (artifact 04 §1).
  def desugar_lambda(n)
    params, locals = block_params(n.parameters)
    fire(:block)
    fire(:"lambda->send")
    [:send, nil, "lambda", [], [:block, params, locals,
                                declared_locals(n, params, locals), stmts(n.body)]]
  end

  # case/when → temp + if/elsif chain over `===`. The subject is evaluated ONCE (bound to a
  # temp), then each `when` value is `pattern === subject`-tested in source order with
  # short-circuit within a multi-value `when` ([V] eval-order verified). A *subjectless*
  # `case` (`case; when cond; …`) truth-tests each `when` condition directly (no `===`).
  # `case x in pat` (pattern matching) is a distinct node (`case_match_node`) — deferred.
  def desugar_case(n)
    fire(:"case->if")
    els = n.else_clause ? stmts(n.else_clause.statements) : nil
    if n.predicate
      t = fresh
      tv = [:var, :local, t]
      chain = when_chain(n.conditions, tv, els)
      [:seq, [:vasgn, :local, t, node(n.predicate)], chain]
    else
      when_chain(n.conditions, nil, els)
    end
  end

  def when_chain(whens, tv, els)
    return els || [:nil] if whens.empty?
    w = whens.first
    [:if, when_cond(w.conditions, tv), stmts(w.statements), when_chain(whens[1..], tv, els)]
  end

  # OR of the per-condition tests, short-circuit; only truthiness reaches the enclosing if.
  # With a subject each test is `(cond === subject)`; subjectless, the condition itself.
  # A splat `when *arr` tests whether ANY element matches — desugared to
  # `[*arr].any? { |w| w === subject }`, where the `[*arr]` array-splat reproduces Ruby's
  # non-array coercion (`when *5` ≡ `when 5`). Splat in a subjectless `when` is deferred.
  def when_cond(conds, tv)
    tests = conds.map do |c|
      if c.type == :splat_node
        fire(:"when-splat")
        arr = [:array, [[:splat, c.expression ? node(c.expression) : nil]]]
        if tv
          # subject present: any element === subject
          w = fresh
          blk = [:block, [[:preq, w]], [], [], [:send, [:var, :local, w], "===", [tv], nil]]
          [:send, arr, "any?", [], blk]
        else
          # subjectless: any element truthy ([*arr].any? with no block)
          [:send, arr, "any?", [], nil]
        end
      elsif tv
        [:send, node(c), "===", [tv], nil]
      else
        node(c)
      end
    end
    tests[0..-2].reverse.reduce(tests[-1]) { |acc, t| [:if, t, [:true], acc] }
  end

  # defined?(expr) — a primitive that inspects the *syntactic* argument (mostly without
  # evaluating it) and returns a describing String or nil. Irreducible, so a head; the
  # inner expr is desugared normally and rendered back inside `defined?(…)`.
  def desugar_defined(n)
    fire(:defined)
    [:defined, node(n.value)]
  end

  # undef foo, bar — remove method definitions. Names are (usually static) symbols; a
  # dynamic-symbol name (`undef :"a#{x}"`) is deferred. `[:undef, [names]]` head.
  def desugar_undef(n)
    fire(:undef)
    names = n.names.map do |nm|
      raise Unsupported, "dynamic undef name :#{nm.type}" unless nm.type == :symbol_node
      nm.unescaped
    end
    [:undef, names]
  end

  # alias new old — a method or $global alias. Both keyword forms (alias_method_node for
  # method names, alias_global_variable_node for $globals) land here. Static names only.
  def desugar_alias(new_n, old_n)
    fire(:alias)
    [:alias, alias_name(new_n), alias_name(old_n)]
  end

  def alias_name(nm)
    case nm.type
    when :symbol_node                 then nm.unescaped
    when :global_variable_read_node   then nm.name.to_s   # carries the $ sigil
    else raise Unsupported, "alias name :#{nm.type}"
    end
  end

  # for x in coll; body; end — iterate, binding the index in the ENCLOSING scope (the index
  # leaks, unlike a block param). Kept as a primitive head rendered back to `for` (a
  # `coll.each { |x| … }` desugaring would wrongly make x block-local). Multi-target
  # (`for a, b in`) supported for simple targets; a rest target is deferred.
  def desugar_for(n)
    fire(:for)
    [:for, for_targets(n.index), node(n.collection), stmts(n.statements)]
  end

  def for_targets(idx)
    if idx.type == :multi_target_node
      raise Unsupported, "for multi-target with rest" if idx.rest || !idx.rights.empty?
      idx.lefts.map { |t| massign_target(t) }
    else
      [massign_target(idx)]
    end
  end

  # A::B / ::B / expr::B — a constant path read. `parent` (the namespace) is nil for a
  # top-level `::B`, else an arbitrary expression node (usually a constant). Irreducible
  # (lexical/relative constant lookup, artifact 03 §5) → a head.
  def desugar_cpath(n)
    fire(:cpath)
    [:cpath, n.parent ? node(n.parent) : nil, n.name.to_s]
  end

  # A::B = v — constant-path assignment. Value of the expression is the RHS (assignment
  # yields RHS natively, so no temp is needed); eval order is parent, then RHS.
  def desugar_cpath_write(n)
    fire(:"cpath-asgn")
    tgt = n.target
    [:cpath_asgn, tgt.parent ? node(tgt.parent) : nil, tgt.name.to_s, node(n.value)]
  end

  # A def/block/lambda parameter list, as a structured list of param nodes (see
  # RubyCore::PARAM_HEADS), built in Ruby's canonical order: requireds, optionals, rest,
  # post-rest requireds, keywords, keyword-rest, block. An optional default (`a = E`) and
  # an optional-keyword default (`a: E`) are arbitrary expressions evaluated lazily in the
  # callee scope at call time — carried as a real desugared node (a flat string couldn't
  # hold them; that is why the slot is structured, not [String], C25). Anonymous `*`/`**`/`&`
  # and destructuring block params (`|(a,b)|`) — nil / deferred respectively.
  def build_params(p)
    return [] if p.nil?
    params = p.requireds.map { |r| req_param(r) }
    p.optionals.each do |o|
      fire(:"opt-param")
      params << [:popt, o.name.to_s, node(o.value)]
    end
    if p.rest
      case p.rest.type
      when :rest_parameter_node then params << [:prest, p.rest.name&.to_s]  # nil = anonymous `*`
      when :implicit_rest_node  then params << [:prest, nil]  # `{ |a,| }` — discard tail (≡ `*`)
      else raise Unsupported, "rest param :#{p.rest.type}"
      end
    end
    params += p.posts.map { |r| req_param(r) }
    p.keywords.each do |k|
      fire(:"kw-param")
      case k.type
      when :required_keyword_parameter_node then params << [:pkey, k.name.to_s, nil]
      when :optional_keyword_parameter_node then params << [:pkey, k.name.to_s, node(k.value)]
      else raise Unsupported, "keyword param :#{k.type}"
      end
    end
    if p.keyword_rest
      case p.keyword_rest.type
      when :keyword_rest_parameter_node
        fire(:"kwrest-param")
        params << [:pkwrest, p.keyword_rest.name&.to_s]  # nil name = bare `**`
      when :forwarding_parameter_node
        fire(:"fwd-param")
        params << [:pfwd]                                # `...` — forwards all args + block
      else raise Unsupported, "keyword-rest :#{p.keyword_rest.type}"
      end
    end
    if p.block
      raise Unsupported, "block param :#{p.block.type}" unless p.block.type == :block_parameter_node
      fire(:"block-capture")
      params << [:pblock, p.block.name&.to_s]          # nil name = anonymous `&`
    end
    params
  end

  def req_param(r)
    case r.type
    when :required_parameter_node then [:preq, r.name.to_s]
    when :multi_target_node       then destr_param(r)   # `|(a, b)|` destructuring
    else raise Unsupported, "non-simple param :#{r.type}"
    end
  end

  # A destructuring block param `|(a, b)|` → [:pdestr, [sub-params]]. Sub-elements are
  # required params, a nested destructure, or a rest (`|(a, *b)|`). Rendered back as
  # `(a, b)`, so the block still auto-splats a single array argument. C29.
  def destr_param(mt)
    fire(:"destructure-param")
    subs = mt.lefts.map { |t| req_param(t) }
    if mt.rest
      raise Unsupported, "destructure rest :#{mt.rest.type}" unless mt.rest.type == :splat_node
      subs << [:prest, mt.rest.expression&.name&.to_s]
    end
    subs += mt.rights.map { |t| req_param(t) }
    [:pdestr, subs]
  end

  def andor(n, and_kind:)
    left  = node(n.left)
    right = node(n.right)
    fire(and_kind ? :"and->if" : :"or->if")

    if @inject_bug
      # NAIVE (buggy) form: evaluates `left` twice. Only under DESUGAR_BUG=1.
      return and_kind ? [:if, left, right, left] : [:if, left, left, right]
    end

    t = fresh
    tvar = [:var, :local, t]
    branch = and_kind ? [:if, tvar, right, tvar] : [:if, tvar, tvar, right]
    [:seq, [:vasgn, :local, t, left], branch]
  end

  def desugar_def(n)
    params = build_params(n.parameters)
    recv = n.receiver ? node(n.receiver) : nil
    fire(recv ? :defs : :def)
    @fn_depth += 1
    begin
      body = stmts(n.body)
    ensure
      @fn_depth -= 1
    end
    recv ? [:defs, recv, n.name.to_s, params, body] : [:def, n.name.to_s, params, body]
  end

  # A constant name in *definition* position (class/module name): either a simple constant
  # (a String, `class Foo`) or a constant-path node (`class A::B` — a [:cpath, base, name],
  # defining `B` inside the namespace `A`; base nil for `class ::B`). Same head as a cpath
  # read (C27).
  def const_def_name(cpath)
    case cpath.type
    when :constant_read_node then cpath.name.to_s
    when :constant_path_node then desugar_cpath(cpath)
    else raise Unsupported, "constant-path name :#{cpath.type}"
    end
  end

  # class Foo < Super; body; end. Keep as a core head rendered to the keyword form — do NOT
  # desugar to `Foo = Class.new`, which changes the lexical cref/self of the body (C18).
  def desugar_class(n)
    name = const_def_name(n.constant_path)
    sup = n.superclass ? node(n.superclass) : nil
    fire(:class)
    [:class, name, sup, class_body(n.body)]
  end

  def desugar_module(n)
    name = const_def_name(n.constant_path)
    fire(:module)
    [:module, name, class_body(n.body)]
  end

  # class << obj; body; end (singleton/eigenclass reopening).
  def desugar_sclass(n)
    fire(:sclass)
    [:sclass, node(n.expression), class_body(n.body)]
  end

  # A class/module/sclass body is a StatementsNode (or nil), but may itself be a BeginNode
  # when the body uses `begin`/`rescue` at the top of the definition — route through stmts
  # (C11 already tolerates a non-StatementsNode body).
  def class_body(body)
    stmts(body)
  end

  # begin; body; rescue …; else …; ensure …; end.
  # Shape: [:begin, body, [rescues], else_or_nil, ensure_or_nil];
  # rescue = [[exc_class_nodes], ref_or_nil, handler]. Bare rescue = empty exc list
  # (matches StandardError; verified [V] adversarial seed) + default handler.
  def desugar_begin(n)
    fire(:begin)
    body = stmts(n.statements)
    rescues = []
    rc = n.rescue_clause
    while rc
      excs = rc.exceptions.map { |e| arg_node(e) }   # `rescue *classes` — splat allowed
      ref = rc.reference ? massign_target(rc.reference) : nil
      rescues << [excs, ref, stmts(rc.statements)]
      rc = rc.subsequent
    end
    els = n.else_clause ? stmts(n.else_clause.statements) : nil
    ens = n.ensure_clause ? stmts(n.ensure_clause.statements) : nil
    [:begin, body, rescues, els, ens]
  end

  # `expr rescue fallback` => begin expr; rescue; fallback; end (one bare rescue).
  def desugar_rescue_modifier(n)
    fire(:"rescue-mod->begin")
    [:begin, node(n.expression), [[[], nil, node(n.rescue_expression)]], nil, nil]
  end

  # Explicit super(...) — incl. super() (empty args). NOT the same as bare `super`, which
  # forwards the enclosing method's args (that's forwarding_super_node -> :zsuper).
  def desugar_super(n)
    fire(:super)
    args = n.arguments ? n.arguments.arguments.map { |a| arg_node(a) } : []
    block = call_block(n.block)
    [:super, args, block]
  end

  def desugar_zsuper(n)
    fire(:zsuper)
    [:zsuper, call_block(n.block)]
  end

  # while/until. The `begin … end while C` / `… until C` *modifier* form (Prism's
  # `begin_modifier?`) is a do-while: the body runs ONCE before the first condition test.
  # A [:while] head has no such flag, and desugaring by duplicating the body is wrong
  # (a `next`/`break` in the first copy wouldn't be in a loop) — so it is deferred.
  # while/until. The `begin … end while C` / `… until C` *modifier* form (Prism's
  # `begin_modifier?`) is a do-while: the body runs ONCE before the first condition test.
  # It gets its own head `[:dowhile, body, cond]` (a plain `[:while]` has no run-once flag,
  # and duplicating the body would break a `next`/`break` in the first copy). `until` is
  # rendered by negating the condition (do-while always renders as `while`). C29.
  def desugar_while(n, negate:)
    pred = negate ? negate(node(n.predicate)) : node(n.predicate)
    body = stmts(n.statements)
    if n.begin_modifier?
      fire(:dowhile)
      [:dowhile, body, pred]
    else
      fire(negate ? :"until->while" : :while)
      [:while, pred, body]
    end
  end

  def desugar_hash(n)
    fire(:hash)
    pairs = n.elements.map do |el|
      raise Unsupported, "hash element :#{el.type}" unless el.type == :assoc_node
      [node(el.key), node(el.value)]
    end
    [:hash, pairs]
  end

  # return/break/next. Top-level `return` terminates the whole script (Ruby 2.4+), which
  # would bypass the observation wrapper (implementation-choices.md C7), so `return` is
  # allowed only inside a def. Splat in the argument list is deferred with splat generally.
  def desugar_jump(n, kind)
    raise Unsupported, "top-level return" if kind == :return && @fn_depth.zero?
    args = n.arguments&.arguments || []
    args.each { |a| raise Unsupported, "splat in #{kind}" if a.type == :splat_node }
    val = case args.length
          when 0 then nil
          when 1 then node(args.first)
          else [:array, args.map { |a| node(a) }]
          end
    fire(kind)
    [kind, val]
  end

  # Multiple assignment. Evaluate the RHS once into a temp array, then distribute by index
  # (positive for lefts, a runtime-length range for the rest, and front-to-back for
  # post-rest rights to match Ruby's underflow rule). The RHS is either an explicit value
  # list (`a, b = 1, *r`, splat-capable) or a single value (`a, b = x`) coerced via
  # `Array.try_convert(x) || [x]` (C28). **The value of the whole massign is the RHS as
  # written** — the array *literal* for a value list, or the *raw* single RHS (`(* = 1)` is
  # `1`, not `[1]`) — NOT the distributed/coerced array; `massign_rhs_array` returns both
  # the temp-array expression and that result value.
  def desugar_massign(n)
    fire(:massign)
    t = fresh
    tv = [:var, :local, t]
    arr_expr, result = massign_rhs_array(n.value, tv)
    stmts = [[:vasgn, :local, t, arr_expr]]
    distribute(n.lefts, n.rest, n.rights, tv, stmts)
    [:seq, *stmts, result]
  end

  # Distribute a temp array `tv` across left targets (front-indexed), an optional rest, and
  # post-rest right targets. Post-rest rights are filled front-to-back after the rest's
  # runtime share — matching Ruby's underflow rule (`*a,b,c = [0]` => a=[], b=0, c=nil),
  # which negative indexing gets wrong. Any target may itself be a nested destructure
  # (`(a,b),c = …`), handled recursively by `assign_target`.
  def distribute(lefts, rest, rights, tv, stmts)
    ln = lefts.length
    rn = rights.length
    lefts.each_with_index { |tn, i| assign_target(tn, index_get(tv, i), stmts) }

    if rest
      # `a, = x` uses an implicit_rest_node (a nameless rest that discards) — treat like an
      # anonymous `*` (assigns nothing). A real `*rest` is a splat_node.
      unless %i[splat_node implicit_rest_node].include?(rest.type)
        raise Unsupported, "massign rest :#{rest.type}"
      end
      rl = fresh
      len_minus = sub(sub([:send, tv, "length", [], nil], [:int, ln]), [:int, rn])
      stmts << [:vasgn, :local, rl, [:send, [:array, [len_minus, [:int, 0]]], "max", [], nil]]
      if rest.type == :splat_node && rest.expression   # named rest; `*`/`a,=` assign nothing
        slice = [:send, tv, "[]", [[:int, ln], [:var, :local, rl]], nil]
        assign_target(rest.expression, [:send, slice, "to_a", [], nil], stmts) # nil-slice -> []
      end
      rights.each_with_index do |tn, j|
        idx = add(add([:var, :local, rl], [:int, ln]), [:int, j]) # rest_len + #lefts + j
        assign_target(tn, [:send, tv, "[]", [idx], nil], stmts)
      end
    else
      # No rest: any rights are just further front-indexed targets.
      rights.each_with_index { |tn, j| assign_target(tn, index_get(tv, ln + j), stmts) }
    end
  end

  # Assign a (desugared) value expression to one massign target, appending statements. A
  # nested target `(a, b)` recursively coerces the value to an array (same to_ary-or-wrap as
  # a single-RHS massign) and distributes into its sub-targets.
  def assign_target(tnode, val, stmts)
    if tnode.type == :multi_target_node
      st = fresh
      stmts << [:vasgn, :local, st, coerce_core_to_array(val)]
      distribute(tnode.lefts, tnode.rest, tnode.rights, [:var, :local, st], stmts)
    else
      k, nm = massign_target(tnode)
      stmts << target_write(k, nm, val)
    end
  end

  # Returns [array_expr, result_value] for a massign RHS. `array_expr` is bound to the temp
  # array that targets distribute from; `result_value` is the value of the whole massign
  # expression (the RHS as written). For an explicit value list (`a, b = 1, *r`) both are
  # the array literal (result = the temp `tv`). For a *single* RHS (`a, b = x`) the array is
  # `Array.try_convert(x) || [x]` (Ruby's to_ary-or-wrap coercion, [V] verified) but the
  # result value is the *raw* x — so x is bound to a temp `r` and result = that `r`.
  def massign_rhs_array(value, tv)
    return [[:array, value.elements.map { |v| arg_node(v) }], tv] if value.type == :array_node

    fire(:"massign-to_ary")
    r = fresh
    rv = [:var, :local, r]
    [[:seq, [:vasgn, :local, r, node(value)], coerce_core_to_array(rv)], rv]
  end

  # Coerce a core value expression to an Array the way Ruby massign does — use it (or its
  # to_ary) if array-convertible, else wrap `[x]`. The value is expected to be side-effect-
  # free here (a temp read or an index get); try_convert is bound to a temp regardless.
  def coerce_core_to_array(v)
    tc = fresh
    tcv = [:var, :local, tc]
    [:seq,
     [:vasgn, :local, tc, [:send, [:const, "Array"], "try_convert", [v], nil]],
     [:if, tcv, tcv, [:array, [v]]]]
  end

  def index_get(tv, i)
    [:send, tv, "[]", [[:int, i]], nil]
  end

  def add(a, b) = [:send, a, "+", [b], nil]
  def sub(a, b) = [:send, a, "-", [b], nil]

  def massign_target(t)
    case t.type
    when :local_variable_target_node    then [:local, t.name.to_s]
    when :instance_variable_target_node then [:ivar, t.name.to_s]
    when :global_variable_target_node   then [:gvar, t.name.to_s]
    when :class_variable_target_node    then [:cvar, t.name.to_s]
    when :constant_target_node          then [:const, t.name.to_s]
    else raise Unsupported, "massign target :#{t.type}"
    end
  end

  def desugar_if(n)
    fire(:if)
    els = else_of(n.subsequent)
    [:if, node(n.predicate), stmts(n.statements), els]
  end

  def desugar_unless(n)
    fire(:"unless->if")
    els = n.else_clause ? stmts(n.else_clause.statements) : nil
    [:if, negate(node(n.predicate)), stmts(n.statements), els]
  end

  # Prism: an if's `subsequent` is nil, an ElseNode, or another IfNode (elsif).
  def else_of(sub)
    return nil if sub.nil?
    return stmts(sub.statements) if sub.type == :else_node
    return desugar_if(sub) if sub.type == :if_node

    raise Unsupported, "if subsequent :#{sub.type}"
  end

  # Read/write builders for a variable-or-constant target.
  def target_read(kind, name)
    kind == :const ? [:const, name] : [:var, kind, name]
  end

  def target_write(kind, name, val)
    kind == :const ? [:casgn, name, val] : [:vasgn, kind, name, val]
  end

  # v ||= e  =>  if v then v else (v = e)   ;   v &&= e  =>  if v then (v = e) else v
  # Only for local/ivar/gvar, where reading an unset variable yields nil (no error).
  # const/cvar ||=/&&= need `defined?` semantics (an unset read *raises*) — deferred.
  def logic_write(n, kind, or_kind:)
    name = n.name.to_s
    fire(or_kind ? :"or-write" : :"and-write")
    rd = target_read(kind, name)
    wr = target_write(kind, name, node(n.value))
    or_kind ? [:if, rd, rd, wr] : [:if, rd, wr, rd]
  end

  # v <op>= e  =>  v = (v <op> e). Variable/constant reads are side-effect-free, so no
  # temp is needed (indexed/attr op-assign, which are, are handled separately / deferred).
  def op_write(n, kind)
    name = n.name.to_s
    op = n.binary_operator.to_s
    fire(:"op-write")
    newval = [:send, target_read(kind, name), op, [node(n.value)], nil]
    target_write(kind, name, newval)
  end

  # 1..5 => ::Range.new(1, 5, false) ; 1...5 => ::Range.new(1, 5, true) ; endless/beginless
  # use nil endpoints. Behavior-identical to the literal — *once the receiver is written
  # absolutely*. A range literal is a parser node in Ruby and consults no constant at all;
  # lowering it to a send over a plain `Range` constant reintroduced a lookup Ruby never
  # performs, so any lexically enclosing `Range` constant hijacked the literal:
  #
  #     module M; Range = 5; def self.f = (1..2); end     # CRuby 1..2, model NoMethodError
  #
  # Not hypothetical — the prelude's own sorbet shim defines `T::Range`, so every range
  # literal inside `module T` broke (found writing L127's `string_truncate_middle`). `::Range`
  # (a `cpath` with no base) skips the lexical chain and resolves on Object, which closes
  # every shadow except a reassignment of the *toplevel* constant. C37.
  def desugar_range(n)
    fire(:"range->send")
    lo = n.left ? node(n.left) : [:nil]
    hi = n.right ? node(n.right) : [:nil]
    excl = n.exclude_end? ? [:true] : [:false]
    [:send, [:cpath, nil, "Range"], "new", [lo, hi, excl], nil]
  end

  # 2r => Rational(2, 1) ; 2.5r => Rational(5, 2). Uses the literal's exact value, so it
  # is precise even for float-derived rationals.
  def desugar_rational(n)
    fire(:"rational->send")
    r = n.value
    [:send, nil, "Rational", [[:int, r.numerator], [:int, r.denominator]], nil]
  end

  # 3i => Complex(0, 3) ; 2.5i => Complex(0, 2.5). Imag part may be Integer/Float/Rational.
  def desugar_imaginary(n)
    fire(:"imaginary->send")
    [:send, nil, "Complex", [numeric_lit(n.value.real), numeric_lit(n.value.imaginary)], nil]
  end

  def numeric_lit(v)
    case v
    when Integer  then [:int, v]
    when Float    then [:flt, v]
    when Rational then [:send, nil, "Rational", [[:int, v.numerator], [:int, v.denominator]], nil]
    else raise Unsupported, "imaginary component #{v.class}"
    end
  end

  def desugar_array(n)
    fire(:array)
    [:array, n.elements.map { |el| arg_node(el) }]
  end

  # "a#{e}b"  =>  (("a") + String(e)) + ("b")   (left-to-right, rb_obj_as_string)
  def interp(n)
    fire(:interp)
    interp_concat(n.parts)
  end

  # `rb_obj_as_string(e)` as RubyCore: a value that is *already* a String (or subclass)
  # is used **verbatim** — a redefined `String#to_s` is NOT called — otherwise `to_s` is
  # called. `Kernel#String(e)` is NOT equivalent: it coerces via `to_str` first (which
  # dispatches through `method_missing` / a user `to_str`), so `String(o) != "#{o}"` for
  # such objects [V] (found by tier-1 fuzzing; see difftest N22/N23). Model it exactly as
  # `t = e; String === t ? t : t.__as_string` (t bound once; `String ===` is a C-level type
  # check, no method dispatch). Uses only seq/if/vasgn/var/send/const — Lean-supported heads.
  #
  # The cold arm is a **runtime-support call**, not `t.to_s` (C38): `rb_obj_as_string` does
  # not stop at `to_s`, it checks the *result* and falls back to `#<C:0x…>` when it is not a
  # String. That third step needs `rb_any_to_s`, which has no Ruby-level name, so it lives
  # in `Object#__as_string` — supplied by the model's prelude and by `Observe::WRAPPER` for
  # the round-trip's plain-CRuby side. The fast arm stays inline so an already-String
  # interpolation still costs no frame.
  def as_string(e)
    t = fresh
    check = [:send, [:const, "String"], "===", [[:var, :local, t]], nil]
    [:seq, [:vasgn, :local, t, e],
           [:if, check, [:var, :local, t],
                        [:send, [:var, :local, t], "__as_string", [], nil]]]
  end

  # Shared string-interpolation concatenation for interpolated strings, symbols, and regex
  # sources. Each part becomes a String and is `+`-chained left to right.
  def interp_concat(parts)
    pieces = parts.map do |part|
      case part.type
      when :string_node
        [:str, part.unescaped]
      when :embedded_statements_node
        # A control-flow jump inside #{...} fires before the string is built; the
        # Linearize pass hoists any unconditional jump out of this operand position.
        as_string(stmts(part.statements))
      when :embedded_variable_node
        # "#@x" / "#$g" — an ivar/gvar interpolation (no braces).
        as_string(node(part.variable))
      when :interpolated_string_node
        # Adjacent implicit concatenation ("a" "b#{c}") nests an interpolated string.
        interp_concat(part.parts)
      else
        raise Unsupported, "interp part :#{part.type}"
      end
    end
    return [:str, ""] if pieces.empty?

    pieces.reduce { |acc, p| [:send, acc, "+", [p], nil] }
  end

  # /pat/imx => Regexp.new(source, opts). The source is a literal String (plain) or the
  # interpolated concatenation (`/a#{e}b/`); opts is the packed flag integer (IGNORECASE=1,
  # EXTENDED=2, MULTILINE=4). [V] Regexp.new(unescaped, opts) reproduces .source + .options
  # exactly. (The literal-regex-on-LHS-of-`=~` named-capture-to-local magic is not modeled;
  # the round-trip flags any program that relies on it.)
  def desugar_regex(n)
    fire(:regex)
    src = n.type == :regular_expression_node ? [:str, n.unescaped] : interp_concat(n.parts)
    # `/u`, `/e`, `/s` fix the *encoding* of the pattern, which `Regexp.new`'s integer
    # option word cannot express (it would need a source String in that encoding), so they
    # gate rather than being silently dropped. `/n` is `Regexp::NOENCODING` (32) and does
    # round-trip. `/o` (interpolate-once) is handled at the call site, not here. (C33.)
    if n.euc_jp? || n.windows_31j? || n.utf_8?
      raise Unsupported, "regex encoding flag (/u, /e, /s — not expressible as Regexp.new options)"
    end
    opts = (n.ignore_case? ? 1 : 0) | (n.extended? ? 2 : 0) | (n.multi_line? ? 4 : 0) |
           (n.ascii_8bit? ? 32 : 0)
    # `::Regexp`, not `Regexp` — a regex literal consults no constant in Ruby, so the
    # lowering must not either (C37, same as the range literal above).
    lit = [:send, [:cpath, nil, "Regexp"], "new", [src, [:int, opts]], nil]
    n.once? ? once_cached(lit) : lit
  end

  # `/…/o` — compile the literal *once*, at first evaluation, and return that same object
  # on every later evaluation without re-running the interpolations. The cache in CRuby is
  # per literal *site* and global (not per receiver, not per thread), so a gensym'd global
  # is an exact model: `$g ? $g : ($g = Regexp.new(…))`, which is the shape `logic_write`
  # already emits for `$g ||= e` — so the round-trip re-desugars to itself. A Regexp is
  # never nil/false, so the truthiness test is a faithful "already compiled?". (C33.)
  def once_cached(lit)
    g = "$__dt_rx#{@gensym += 1}"
    rd = [:var, :gvar, g]
    [:if, rd, rd, [:vasgn, :gvar, g, lit]]
  end

  # :"a#{e}b" => (interp string).to_sym — behavior-identical dynamic symbol.
  def desugar_isym(n)
    fire(:isym)
    [:send, interp_concat(n.parts), "to_sym", [], nil]
  end

  # Indexed op-assign — a[i] += v / a[i] ||= v / a[i] &&= v. The receiver and every index
  # are evaluated ONCE (cached in temps), preserving eval order and avoiding double side
  # effects. Value of the expression is the new element value (for ||=/&&=, the short-circuit
  # result). C29.
  def desugar_index_write(n, mode)
    fire(:"index-opwrite")
    tr = fresh
    trv = [:var, :local, tr]
    pre = [[:vasgn, :local, tr, node(n.receiver)]]
    idx_vars = (n.arguments ? n.arguments.arguments : []).map do |a|
      ti = fresh
      if a.type == :splat_node
        # cache the splatted array once, re-splat the temp (`a[*idx]` — binding `*idx` to a
        # temp would wrap it into an array and index by the wrong value, C29 harness-caught).
        fire(:splat)
        pre << [:vasgn, :local, ti, a.expression ? node(a.expression) : [:nil]]
        [:splat, [:var, :local, ti]]
      else
        pre << [:vasgn, :local, ti, node(a)]
        [:var, :local, ti]
      end
    end
    read  = [:send, trv, "[]", idx_vars, nil]
    write = ->(val) { [:send, trv, "[]=", idx_vars + [val], nil] }
    [:seq, *pre, *opwrite_body(read, write, mode, n)]
  end

  # Attribute op-assign — a.b += v / a.b ||= v / a.b &&= v. Receiver evaluated once. Safe
  # navigation (`a&.b += v`) is deferred. C29.
  def desugar_attr_write(n, mode)
    raise Unsupported, "safe-navigation op-assign" if n.safe_navigation?
    fire(:"attr-opwrite")
    tr = fresh
    trv = [:var, :local, tr]
    pre = [[:vasgn, :local, tr, node(n.receiver)]]
    read  = [:send, trv, n.read_name.to_s, [], nil]
    write = ->(val) { [:send, trv, n.write_name.to_s, [val], nil] }
    [:seq, *pre, *opwrite_body(read, write, mode, n)]
  end

  # Shared read/write body for op-assign, given a `read` node and a `write` builder. `:op`
  # is `write(read <op> v)`; `:or`/`:and` short-circuit on a cached read. The trailing node
  # of the seq is the expression's value.
  def opwrite_body(read, write, mode, n)
    if mode == :op
      nv = fresh
      nvv = [:var, :local, nv]
      [[:vasgn, :local, nv, [:send, read, n.binary_operator.to_s, [node(n.value)], nil]],
       write.call(nvv), nvv]
    else
      tval = fresh
      tvv = [:var, :local, tval]
      wr = write.call(node(n.value))
      cond = mode == :or ? [:if, tvv, tvv, wr] : [:if, tvv, wr, tvv]
      [[:vasgn, :local, tval, read], cond]
    end
  end
end
