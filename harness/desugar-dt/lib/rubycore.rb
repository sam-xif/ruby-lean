# frozen_string_literal: true

# RubyCore node definitions and well-formedness (`is_core`).
#
# Nodes are tagged S-expressions (arrays with a leading Symbol head), per
# implementation-choices.md C2. This module is the single source of truth for which
# heads are part of the modeled fragment.
module RubyCore
  # head => arity/shape description (for documentation; is_core checks heads + recursion)
  HEADS = {
    int:   "[:int, Integer]",
    flt:   "[:flt, Float]",
    str:   "[:str, String]",           # literal string, no interpolation
    sym:   "[:sym, String]",
    true:  "[:true]",
    false: "[:false]",
    nil:   "[:nil]",
    self:  "[:self]",
    var:   "[:var, kind, name]      kind ∈ :local|:ivar|:cvar|:gvar; name carries any sigil",
    vasgn: "[:vasgn, kind, name, expr]",
    const: "[:const, name]",
    casgn: "[:casgn, name, expr]",
    cpath: "[:cpath, base_or_nil, name]",         # A::B (base a node) / ::B (base nil, top-level)
    cpath_asgn: "[:cpath_asgn, base_or_nil, name, expr]",  # A::B = expr
    send:  "[:send, recv_or_nil, mname, [args], block_or_nil]",
    block: "[:block, [params], [block_locals], body]",  # {|params; locals| body}; params are param-nodes
    yield: "[:yield, [args]]",                               # yield to the current block
    if:    "[:if, cond, then, else_or_nil]",
    while: "[:while, cond, body]",
    def:   "[:def, name, [params], body]",              # params are param-nodes (see PARAM_HEADS)
    array: "[:array, [elems]]",
    hash:  "[:hash, [[key, val], ...]]",
    splat: "[:splat, expr_or_nil]",     # only valid as a send-arg / array element (`*e`)
    fwd:   "[:fwd]",                    # `...` argument forwarding — only valid as a send arg
    kwargs: "[:kwargs, [elems]]",       # only valid as the last send/super arg; elem = [k,v] (assoc) | [:kwsplat, e_or_nil]
    blockpass: "[:blockpass, expr_or_nil]",  # only valid in a send/super block slot (`&e`); nil = anonymous `&`
    return: "[:return, expr_or_nil]",   # primitive non-local control
    break:  "[:break, expr_or_nil]",
    next:   "[:next, expr_or_nil]",
    retry:  "[:retry]",                 # re-run the enclosing begin body
    # object-model core (C12 category d): class/module bodies are evaluated with a fresh
    # cref + self, so these are irreducible primitives, NOT sugar for Class.new (see C18).
    class:  "[:class, name, super_or_nil, body]",   # name: simple constant String
    module: "[:module, name, body]",
    sclass: "[:sclass, obj, body]",                 # class << obj; body; end
    defs:   "[:defs, recv, name, [param_names], body]",  # def recv.name(params); body; end
    begin:  "[:begin, body, [rescues], else_or_nil, ensure_or_nil]",  # rescue = [[exc_nodes], ref_or_nil, handler]
    super:  "[:super, [args], block_or_nil]",       # explicit super(...) (incl. super() = empty args)
    zsuper: "[:zsuper, block_or_nil]",              # bare super (forwards enclosing args)
    defined: "[:defined, expr]",                    # defined?(expr) — inspects, returns String|nil
    redo:  "[:redo]",                               # re-run the current loop iteration
    undef: "[:undef, [names]]",                     # undef foo, bar  (names carry any sigil)
    alias: "[:alias, new, old]",                    # alias new old   (method or $global names)
    for:   "[:for, [[kind, name], ...], coll, body]",  # for x in coll; body; end (index leaks)
    dowhile: "[:dowhile, body, cond]",              # begin; body; end while cond (run-once)
    seq:   "[:seq, *nodes]"
  }.freeze

  # A rescue clause's `=> target` reference (and massign targets) is a [kind, name] pair,
  # not a node; these are the valid kinds. Reused by the begin well-formedness check.
  TARGET_KINDS = %i[local ivar cvar gvar const].freeze

  # Parameter nodes — a sub-grammar of def/defs/block param slots, NOT top-level heads
  # (they only appear inside a param list). Ordered as Ruby requires: preq, popt, prest,
  # preq (post-rest), pkey, pkwrest, pblock. A `name_or_nil` nil = anonymous (`*`/`**`/`&`);
  # a `default_or_nil` nil for :pkey = a *required* keyword (`f:`).
  #   [:preq, name]                 required positional          a
  #   [:popt, name, default_expr]   optional positional          a = E
  #   [:prest, name_or_nil]         rest                         *a / *
  #   [:pkey, name, default_or_nil] keyword (req if default nil)  a: / a: E
  #   [:pkwrest, name_or_nil]       keyword-rest                 **o / **
  #   [:pblock, name_or_nil]        block-capture                &b / &
  #   [:pfwd]                       argument forwarding          ...
  #   [:pdestr, [sub-params]]       destructuring block param    (a, b)
  PARAM_HEADS = %i[preq popt prest pkey pkwrest pblock pfwd pdestr].freeze

  module_function

  # A class/module definition name is either a simple constant (String) or a constant-path
  # node ([:cpath, base, name], e.g. `class A::B`). nil if valid, else an error string.
  def const_name_error(name)
    return nil if name.is_a?(String)
    return "name must be String or cpath" unless name.is_a?(Array) && name[0] == :cpath
    explain(name)
  end

  # nil if the param list is well-formed, else a short error string.
  def params_error(params)
    return "params not Array" unless params.is_a?(Array)
    params.each do |p|
      return "param not array: #{p.inspect}" unless p.is_a?(Array) && p[0].is_a?(Symbol)
      return "unknown param head :#{p[0]}" unless PARAM_HEADS.include?(p[0])
      case p[0]
      when :preq, :pkey
        return "#{p[0]} name not String" unless p[1].is_a?(String)
        return "popt/pkey default: #{explain(p[2])}" if p[0] == :pkey && p[2] && !is_core?(p[2])
      when :popt
        return "popt name not String" unless p[1].is_a?(String)
        x = explain(p[2]); return "popt default: #{x}" if x
      when :prest, :pkwrest, :pblock
        return "#{p[0]} name not String/nil" unless p[1].nil? || p[1].is_a?(String)
      when :pfwd
        return ":pfwd takes no fields" unless p.length == 1
      when :pdestr
        return "pdestr subs: #{params_error(p[1])}" if params_error(p[1])
      end
    end
    nil
  end

  # Structural well-formedness: every node's head is in the fragment and children
  # recursively check out. Returns true/false; use `explain` for the first offending node.
  def is_core?(node)
    explain(node).nil?
  end

  # Returns nil if well-formed, else a short string naming the first problem.
  def explain(node)
    return "not an array: #{node.inspect}" unless node.is_a?(Array) && node[0].is_a?(Symbol)

    head = node[0]
    return "unknown head :#{head}" unless HEADS.key?(head)

    case head
    when :int    then node[1].is_a?(Integer) ? nil : "int payload not Integer"
    when :flt    then node[1].is_a?(Float) ? nil : "flt payload not Float"
    when :str, :sym then node[1].is_a?(String) ? nil : ":#{head} payload not String"
    when :true, :false, :nil, :self then node.length == 1 ? nil : ":#{head} takes no children"
    when :var
      _, kind, name = node
      return "var kind invalid: #{kind.inspect}" unless %i[local ivar cvar gvar].include?(kind)
      name.is_a?(String) ? nil : "var name not String"
    when :vasgn
      _, kind, name, e = node
      return "vasgn kind invalid: #{kind.inspect}" unless %i[local ivar cvar gvar].include?(kind)
      return "vasgn name not String" unless name.is_a?(String)
      explain(e)
    when :const  then node[1].is_a?(String) ? nil : "const name not String"
    when :casgn  then node[1].is_a?(String) ? explain(node[2]) : "casgn name not String"
    when :cpath
      _, base, name = node
      return "cpath name not String" unless name.is_a?(String)
      base && !is_core?(base) ? "cpath base: #{explain(base)}" : nil
    when :cpath_asgn
      _, base, name, e = node
      return "cpath_asgn name not String" unless name.is_a?(String)
      return "cpath_asgn base: #{explain(base)}" if base && !is_core?(base)
      explain(e)
    when :send
      _, recv, mname, args, blk = node
      return "send mname not String" unless mname.is_a?(String)
      return "send args not Array" unless args.is_a?(Array)
      return explain(recv) if recv && !is_core?(recv)
      args.each { |a| e = explain(a); return "send arg: #{e}" if e }
      blk && !is_core?(blk) ? explain(blk) : nil
    when :block
      _, params, locals, body = node
      return "block params: #{params_error(params)}" if params_error(params)
      return "block locals not Array of String" unless locals.is_a?(Array) && locals.all? { |p| p.is_a?(String) }
      explain(body)
    when :yield
      args = node[1]
      return "yield args not Array" unless args.is_a?(Array)
      args.each { |a| x = explain(a); return "yield arg: #{x}" if x }
      nil
    when :if
      _, c, t, e = node
      [c, t, (e || [:nil])].each { |n| x = explain(n); return "if child: #{x}" if x }
      nil
    when :while
      _, c, b = node
      (x = explain(c)) ? "while cond: #{x}" : explain(b)
    when :def
      _, name, params, body = node
      return "def name not String" unless name.is_a?(String)
      return "def params: #{params_error(params)}" if params_error(params)
      explain(body)
    when :array
      elems = node[1]
      return "array payload not Array" unless elems.is_a?(Array)
      elems.each { |n| x = explain(n); return "array elem: #{x}" if x }
      nil
    when :hash
      pairs = node[1]
      return "hash payload not Array" unless pairs.is_a?(Array)
      pairs.each do |kv|
        return "hash pair not [k,v]" unless kv.is_a?(Array) && kv.length == 2
        x = explain(kv[0]); return "hash key: #{x}" if x
        y = explain(kv[1]); return "hash val: #{y}" if y
      end
      nil
    when :return, :break, :next
      node[1].nil? ? nil : explain(node[1])
    when :retry
      node.length == 1 ? nil : ":retry takes no children"
    when :class
      _, name, sup, body = node
      return "class name: #{const_name_error(name)}" if const_name_error(name)
      return "class super: #{explain(sup)}" if sup && !is_core?(sup)
      explain(body)
    when :module
      _, name, body = node
      return "module name: #{const_name_error(name)}" if const_name_error(name)
      explain(body)
    when :sclass
      _, obj, body = node
      (x = explain(obj)) ? "sclass obj: #{x}" : explain(body)
    when :defs
      _, recv, name, params, body = node
      return "defs recv: #{explain(recv)}" if !is_core?(recv)
      return "defs name not String" unless name.is_a?(String)
      return "defs params: #{params_error(params)}" if params_error(params)
      explain(body)
    when :begin
      _, body, rescues, els, ens = node
      return "begin body: #{explain(body)}" unless is_core?(body)
      return "begin rescues not Array" unless rescues.is_a?(Array)
      rescues.each do |r|
        return "rescue not [excs, ref, handler]" unless r.is_a?(Array) && r.length == 3
        excs, ref, handler = r
        return "rescue excs not Array" unless excs.is_a?(Array)
        excs.each { |e| x = explain(e); return "rescue exc: #{x}" if x }
        unless ref.nil?
          return "rescue ref not [kind, name]" unless ref.is_a?(Array) && ref.length == 2 && ref[1].is_a?(String)
          return "rescue ref kind invalid: #{ref[0].inspect}" unless TARGET_KINDS.include?(ref[0])
        end
        x = explain(handler); return "rescue handler: #{x}" if x
      end
      return "begin else: #{explain(els)}" if els && !is_core?(els)
      ens && !is_core?(ens) ? "begin ensure: #{explain(ens)}" : nil
    when :super
      _, args, blk = node
      return "super args not Array" unless args.is_a?(Array)
      args.each { |a| x = explain(a); return "super arg: #{x}" if x }
      blk && !is_core?(blk) ? explain(blk) : nil
    when :zsuper
      node[1] && !is_core?(node[1]) ? explain(node[1]) : nil
    when :defined
      explain(node[1])
    when :redo
      node.length == 1 ? nil : ":redo takes no children"
    when :undef
      names = node[1]
      return "undef names not Array of String" unless names.is_a?(Array) && names.all? { |x| x.is_a?(String) }
      nil
    when :alias
      node[1].is_a?(String) && node[2].is_a?(String) ? nil : "alias names not String"
    when :for
      _, targets, coll, body = node
      return "for targets not Array" unless targets.is_a?(Array) && !targets.empty?
      targets.each do |kn|
        return "for target not [kind, name]" unless kn.is_a?(Array) && kn.length == 2 && kn[1].is_a?(String)
        return "for target kind invalid: #{kn[0].inspect}" unless TARGET_KINDS.include?(kn[0])
      end
      return "for coll: #{explain(coll)}" unless is_core?(coll)
      explain(body)
    when :dowhile
      _, body, cond = node
      (x = explain(body)) ? "dowhile body: #{x}" : explain(cond)
    when :splat
      node[1].nil? ? nil : explain(node[1])
    when :fwd
      node.length == 1 ? nil : ":fwd takes no children"
    when :kwargs
      elems = node[1]
      return "kwargs payload not Array" unless elems.is_a?(Array)
      elems.each do |el|
        return "kwargs elem not Array" unless el.is_a?(Array)
        if el[0] == :kwsplat
          return "kwsplat expr: #{explain(el[1])}" if el[1] && !is_core?(el[1])
        else
          return "kwargs assoc not [k,v]" unless el.length == 2
          x = explain(el[0]); return "kwargs key: #{x}" if x
          y = explain(el[1]); return "kwargs val: #{y}" if y
        end
      end
      nil
    when :blockpass
      node[1].nil? ? nil : explain(node[1])
    when :seq
      body = node[1..]
      return "empty seq" if body.empty?
      body.each { |n| x = explain(n); return "seq child: #{x}" if x }
      nil
    end
  end

  # Structural equality (used by the normal-form / idempotence check).
  def eq?(a, b)
    a == b
  end
end
