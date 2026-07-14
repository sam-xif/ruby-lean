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
    opt-param kw-param kwrest-param kwargs
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
    when :float_node              then fire(:flt);  [:flt, n.value]
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
    else
      raise Unsupported, "node type :#{n.type}"
    end
  end

  private

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

    fire(:send)
    recv  = n.receiver ? node(n.receiver) : nil
    args  = n.arguments ? n.arguments.arguments.map { |a| arg_node(a) } : []
    block = call_block(n.block)
    [:send, recv, n.name.to_s, args, block]
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
    [:block, params, locals, stmts(b.body)]
  end

  # Positional params + block-local names (`|params; locals|`) from a
  # BlockParametersNode (block or lambda), or [[], []] when absent.
  def block_params(bp)
    return [[], []] if bp.nil?
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
    [:send, nil, "lambda", [], [:block, params, locals, stmts(n.body)]]
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
      raise Unsupported, "rest param :#{p.rest.type}" unless p.rest.type == :rest_parameter_node
      params << [:prest, p.rest.name&.to_s]   # nil name = anonymous `*`
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
      raise Unsupported, "keyword-rest :#{p.keyword_rest.type}" unless p.keyword_rest.type == :keyword_rest_parameter_node
      fire(:"kwrest-param")
      params << [:pkwrest, p.keyword_rest.name&.to_s]  # nil name = bare `**`
    end
    if p.block
      raise Unsupported, "block param :#{p.block.type}" unless p.block.type == :block_parameter_node
      fire(:"block-capture")
      params << [:pblock, p.block.name&.to_s]          # nil name = anonymous `&`
    end
    params
  end

  def req_param(r)
    raise Unsupported, "non-simple param :#{r.type}" unless r.type == :required_parameter_node
    [:preq, r.name.to_s]
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

  # A constant name in *definition* position (class/module name). Only simple names are
  # in-fragment; a constant *path* (`class A::B`) is a distinct primitive (lexical vs.
  # relative nesting, artifact 03 §5) and is deferred — clean gate. Constant-path *reads*
  # (namespaced superclass `< A::B`) are likewise deferred for now (C19).
  def const_def_name(cpath)
    raise Unsupported, "constant-path name :#{cpath.type}" unless cpath.type == :constant_read_node
    cpath.name.to_s
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
      excs = rc.exceptions.map { |e| node(e) }
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
  def desugar_while(n, negate:)
    raise Unsupported, "do-while (begin-modifier loop)" if n.begin_modifier?
    pred = negate ? negate(node(n.predicate)) : node(n.predicate)
    fire(negate ? :"until->while" : :while)
    [:while, pred, stmts(n.statements)]
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

  # Multiple assignment — correct *subset* only: RHS is an explicit value list
  # (array literal from `= e1, e2, ...`), no rest/splat target, no splat in the RHS, and
  # all targets are simple variable/constant targets. Deferred cases (single-RHS to_ary
  # coercion, splat) raise Unsupported. Desugars to: evaluate RHS once into a temp array,
  # then index-assign each target (order-preserving; value of the massign is the array).
  # Multiple assignment. RHS must be an explicit value list (single-RHS `a,b = x` still
  # needs to_ary coercion — deferred). Splat in the RHS list is fine now (array supports
  # it). A rest target `a, *b, c = …` is supported via array slicing. Evaluate RHS once
  # into a temp array, then distribute by index (positive for lefts, a range for the rest,
  # negative for post-rest rights). Value of the massign is the array.
  def desugar_massign(n)
    raise Unsupported, "massign single RHS (needs to_ary coercion)" unless n.value.type == :array_node
    fire(:massign)
    t = fresh
    tv = [:var, :local, t]
    vals = n.value.elements.map { |v| arg_node(v) }
    lefts = n.lefts.map { |x| massign_target(x) }
    rights = n.rights.map { |x| massign_target(x) }
    ln = lefts.length
    rn = rights.length

    stmts = [[:vasgn, :local, t, [:array, vals]]]
    # lefts: front-indexed (nil if underflowing).
    lefts.each_with_index { |(k, nm), i| stmts << target_write(k, nm, index_get(tv, i)) }

    if n.rest
      raise Unsupported, "massign rest :#{n.rest.type}" unless n.rest.type == :splat_node
      # rest_len = [t.length - #lefts - #rights, 0].max ; rest = (t[ln, rest_len]).to_a
      # Post-rest targets are filled front-to-back starting after the rest's share — this
      # matches Ruby's underflow rule (`*a,b,c = [0]` => a=[], b=0, c=nil), which negative
      # indexing gets wrong. So we need the runtime length.
      rl = fresh
      len_minus = sub(sub([:send, tv, "length", [], nil], [:int, ln]), [:int, rn])
      stmts << [:vasgn, :local, rl, [:send, [:array, [len_minus, [:int, 0]]], "max", [], nil]]
      if n.rest.expression   # named rest; anonymous `*` assigns nothing
        rk, rnm = massign_target(n.rest.expression)
        slice = [:send, tv, "[]", [[:int, ln], [:var, :local, rl]], nil]
        stmts << target_write(rk, rnm, [:send, slice, "to_a", [], nil]) # nil-slice -> []
      end
      rights.each_with_index do |(k, nm), j|
        idx = add(add([:var, :local, rl], [:int, ln]), [:int, j]) # rest_len + #lefts + j
        stmts << target_write(k, nm, [:send, tv, "[]", [idx], nil])
      end
    else
      # No rest: any rights are just further front-indexed targets.
      rights.each_with_index { |(k, nm), j| stmts << target_write(k, nm, index_get(tv, ln + j)) }
    end

    [:seq, *stmts, tv]
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

  # 1..5 => Range.new(1, 5, false) ; 1...5 => Range.new(1, 5, true) ; endless/beginless
  # use nil endpoints. Behavior-identical to the literal.
  def desugar_range(n)
    fire(:"range->send")
    lo = n.left ? node(n.left) : [:nil]
    hi = n.right ? node(n.right) : [:nil]
    excl = n.exclude_end? ? [:true] : [:false]
    [:send, [:const, "Range"], "new", [lo, hi, excl], nil]
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

  # "a#{e}b"  =>  (("a") + (e).to_s) + ("b")   (left-to-right, to_s dispatched)
  def interp(n)
    fire(:interp)
    parts = n.parts.map do |part|
      case part.type
      when :string_node
        [:str, part.unescaped]
      when :embedded_statements_node
        # Interpolation uses `rb_obj_as_string`, NOT `to_s`: a value that is *already* a
        # String is used verbatim (a redefined `String#to_s` is NOT called) — [V] verified
        # against CRuby (test_yjit_112/114). `Kernel#String(e)` matches this exactly: it
        # passes Strings through (via to_str) and calls to_s only on non-Strings. A
        # control-flow jump inside #{...} fires before the string is built; the Linearize
        # pass hoists any unconditional jump out of this operand position.
        [:send, nil, "String", [stmts(part.statements)], nil]
      else
        raise Unsupported, "interp part :#{part.type}"
      end
    end
    return [:str, ""] if parts.empty?

    parts.reduce { |acc, p| [:send, acc, "+", [p], nil] }
  end
end
