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
    send:  "[:send, recv_or_nil, mname, [args], block_or_nil]",
    block: "[:block, [param_names], [block_locals], body]",  # {|params; locals| body}
    yield: "[:yield, [args]]",                               # yield to the current block
    if:    "[:if, cond, then, else_or_nil]",
    while: "[:while, cond, body]",
    def:   "[:def, name, [param_names], body]",
    array: "[:array, [elems]]",
    hash:  "[:hash, [[key, val], ...]]",
    splat: "[:splat, expr_or_nil]",     # only valid as a send-arg / array element (`*e`)
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
    seq:   "[:seq, *nodes]"
  }.freeze

  # A rescue clause's `=> target` reference (and massign targets) is a [kind, name] pair,
  # not a node; these are the valid kinds. Reused by the begin well-formedness check.
  TARGET_KINDS = %i[local ivar cvar gvar const].freeze

  module_function

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
    when :send
      _, recv, mname, args, blk = node
      return "send mname not String" unless mname.is_a?(String)
      return "send args not Array" unless args.is_a?(Array)
      return explain(recv) if recv && !is_core?(recv)
      args.each { |a| e = explain(a); return "send arg: #{e}" if e }
      blk && !is_core?(blk) ? explain(blk) : nil
    when :block
      _, params, locals, body = node
      return "block params not Array of String" unless params.is_a?(Array) && params.all? { |p| p.is_a?(String) }
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
      return "def params not Array of String" unless params.is_a?(Array) && params.all? { |p| p.is_a?(String) }
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
      return "class name not String" unless name.is_a?(String)
      return "class super: #{explain(sup)}" if sup && !is_core?(sup)
      explain(body)
    when :module
      _, name, body = node
      name.is_a?(String) ? explain(body) : "module name not String"
    when :sclass
      _, obj, body = node
      (x = explain(obj)) ? "sclass obj: #{x}" : explain(body)
    when :defs
      _, recv, name, params, body = node
      return "defs recv: #{explain(recv)}" if !is_core?(recv)
      return "defs name not String" unless name.is_a?(String)
      return "defs params not Array of String" unless params.is_a?(Array) && params.all? { |p| p.is_a?(String) }
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
    when :splat
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
