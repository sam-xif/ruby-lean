#!/usr/bin/env ruby
# frozen_string_literal: true

# emit_deriv.rb -- the **untrusted** emitter: a sig-stripped AST + signatures,
# out a `Deriv` (`Ratchet/Deriv.lean`).
#
#   emit_deriv.rb --ast build/NNN.ast.json --sigs build/NNN.sigs.json
#   echo '{"ast": <ast>, "sigs": <sigs>}' | emit_deriv.rb
#
# The second form is the one the page uses: there is no filesystem in a wasm
# module, so both inputs arrive as one JSON object on stdin. The first is what
# `scripts/build_corpus.py` calls.
#
# Stage 4 of `scripts/build_corpus.py`'s five, and the only one that has to think.
#
# It began as a line-for-line port of a Python original, written so the browser
# could derive without a Python runtime, and replaced it once the two were shown
# to agree: byte-identical `emit` fields across all 259 rungs through the real
# pipeline, and the gate unchanged at reach 65 / fragment 63 / RATCHET GREEN.
# Two places where the languages differ are commented where they occur (`zip`
# truncation, float packing); both reproduce the original's behaviour.
#
# Nothing here is trusted. the certificate-language note §1: generation owns
# completeness, validation owns soundness. This file may **block** ("I cannot
# build a derivation for this") and it may propose a derivation the checker then
# rejects. It cannot cause a wrong accept, because `validateD` re-derives every
# type it writes down -- which is also why reading signatures off the source
# instead of out of Sorbet (see `read_sigs.rb`) is safe.

require "json"

# --------------------------------------------------------------------------
# `Ty` constructors, in `Ratchet/Ty.lean`'s wire encoding
# --------------------------------------------------------------------------

INT   = { "tag" => "int" }.freeze
BOOL  = { "tag" => "bool" }.freeze
NIL_T = { "tag" => "nilT" }.freeze
SYM   = { "tag" => "sym" }.freeze
FLOAT = { "tag" => "float" }.freeze
NEVER = { "tag" => "never" }.freeze
STR   = { "tag" => "cls", "name" => "String" }.freeze
IVAR0 = { "tag" => "ivar0" }.freeze

def cls(n)          = { "tag" => "cls", "name" => n }
def array_of(t)     = { "tag" => "arrayOf", "elem" => t }
def hash_of(k, v)   = { "tag" => "hashOf", "key" => k, "val" => v }
def nilable(t)      = { "tag" => "nilable", "elem" => t }

# An ivar/capture spine, built right to left (`Ty.ivarCons`).
def spine(pairs)
  pairs.reverse.reduce(IVAR0) do |rest, (name, ty)|
    { "tag" => "ivarCons", "name" => name, "ty" => ty, "rest" => rest }
  end
end

# Mirror `joinT`: structural cases first, then an ordered, deduplicated union.
def join(a, b)
  return b if a == NEVER
  return a if b == NEVER
  return a if a == b
  return nilable(b) if a == NIL_T
  return nilable(a) if b == NIL_T
  return a if a == nilable(b)
  return b if b == nilable(a)

  members = lambda do |t|
    t["tag"] == "union" ? members.call(t["l"]) + members.call(t["r"]) : [t]
  end
  unique = []
  (members.call(a) + members.call(b)).each { |t| unique << t unless unique.include?(t) }
  unique[0...-1].reverse.reduce(unique[-1]) { |out, t| { "tag" => "union", "l" => t, "r" => out } }
end

# Out of the emitter's fragment. The message is the measurement.
class Blocked < StandardError; end

# --------------------------------------------------------------------------
# The builtin signature table
# --------------------------------------------------------------------------
#
# A **subset** of `Ratchet/Judge.lean`'s `PrimSig`, here only so the emitter can
# propose a `Deriv.prim`'s result type. It is not the authority: `check`
# re-derives the row from `PrimSig` itself, so a row missing here costs a block
# and a row wrong here costs a reject.
def prim_ret(recv, m, args)
  t = recv["tag"]
  n = recv["name"]

  if t == "int"
    return INT  if %w[+ - * / <=>].include?(m) && args == [INT]
    return BOOL if %w[< <= > >=].include?(m) && args == [INT]
    return STR  if m == "to_s" && args.empty?
    return BOOL if m == "zero?" && args.empty?
  end

  if t == "cls" && n == "String"
    return STR           if m == "+" && args == [STR]
    return STR           if %w[strip downcase upcase].include?(m) && args.empty?
    return INT           if m == "length" && args.empty?
    return BOOL          if m == "empty?" && args.empty?
    return BOOL          if m == "start_with?" && args == [STR]
    return array_of(STR) if m == "split" && args == [STR]
  end

  if t == "arrayOf"
    return INT                    if m == "length" && args.empty?
    return BOOL                   if m == "empty?" && args.empty?
    return nilable(recv["elem"])  if m == "[]" && args == [INT]
    return recv                   if m == "<<" && args == [recv["elem"]]
  end

  if t == "hashOf"
    return INT                   if m == "length" && args.empty?
    return nilable(recv["val"])  if m == "[]" && args.length == 1
    return recv["val"]           if m == "fetch" && args.length == 1
  end

  return STR  if t == "sym" && m == "to_s" && args.empty?
  return BOOL if t == "bool" && m == "!" && args.empty?

  # `Judge.prim`'s `objEq` row: `==` at an `EqSafe` receiver, argument unconstrained.
  if m == "==" && args.length == 1 &&
     %w[int float bool nilT sym cls hashOf].include?(t)
    return BOOL
  end
  if m == "nil?" && args.empty? &&
     %w[int float bool nilT sym cls arrayOf hashOf].include?(t)
    return BOOL
  end
  nil
end

# --------------------------------------------------------------------------
# The emitter
# --------------------------------------------------------------------------

class Emitter
  def initialize(sigs)
    @sigs = {}                                  # [owner, name] -> {params, ret}
    (sigs["sigs"] || []).each { |s| @sigs[[s["cls"], s["name"]]] = s }
    @dropped = {}
    (sigs["dropped"] || []).each { |d| @dropped[[d["cls"], d["name"]]] = d["why"] }
    @env = {}          # locals
    @ivars = {}        # the current self's ivars
    @cls_ivars = {}    # class name -> [[ivar, ty], ...]
    @supers = {}       # class name -> superclass name
    @self_cls = nil
  end

  # -- helpers ------------------------------------------------------------

  # The declared signature of `owner#name`, inherited if the class does not
  # define it. Sorbet reports the **owner**, so an inherited method is filed
  # under the superclass and the walk is this package's, not the manifest's.
  def sig_for(owner, name)
    cur = owner
    while cur
      key = [cur, name]
      return @sigs[key] if @sigs.key?(key)
      raise Blocked, "#{cur}##{name}: #{@dropped[key]}" if @dropped.key?(key)

      cur = @supers[cur]
    end
    raise Blocked, "no signature for #{owner}##{name}"
  end

  # A declared `Ty.cls C` for a *user* class C, recovered as `Ty.inst C <spine>`.
  # The known gap: a signature says `Point` and carries no ivar spine, but
  # `Ratchet/Ty.lean` types an instance as `.inst name <spine>`. Where the class
  # body has been seen the spine is known; where it has not, the `.cls` stays
  # and the first method call on it blocks.
  def as_inst(t)
    if t["tag"] == "cls" && @cls_ivars.key?(t["name"])
      { "tag" => "inst", "name" => t["name"], "ivars" => spine(@cls_ivars[t["name"]]) }
    else
      t
    end
  end

  # -- the walk -----------------------------------------------------------

  # `node` -> [deriv, type]. Raises `Blocked` outside the fragment.
  def go(node)
    tag = node[0]
    meth = "n_#{tag.gsub("?", "_q")}"
    raise Blocked, "no rule for AST node '#{tag}'" unless respond_to?(meth, true)

    send(meth, node)
  end

  def go_all(nodes)
    ds = []
    ts = []
    nodes.each do |n|
      d, t = go(n)
      ds << d
      ts << t
    end
    [ds, ts]
  end

  private

  # literals
  def n_int(n)   = [{ "rule" => "intLit", "n" => n[1] }, INT]
  def n_str(n)   = [{ "rule" => "strLit", "s" => n[1] }, STR]
  def n_sym(n)   = [{ "rule" => "symLit", "s" => n[1] }, SYM]
  def n_true(_n) = [{ "rule" => "truLit" }, BOOL]
  def n_false(_n) = [{ "rule" => "flsLit" }, BOOL]
  def n_nil(_n)  = [{ "rule" => "nilLit" }, NIL_T]

  def n_self(_n)
    raise Blocked, "`self` outside a class body" if @self_cls.nil?

    [{ "rule" => "selfExpr" },
     { "tag" => "inst", "name" => @self_cls, "ivars" => spine(@ivars.to_a) }]
  end

  def n_flt(n)
    # `Expr.flt` carries IEEE-754 bits; the AST carries the double. Python does
    # this with struct '<d' -> '<Q'; "E" is the same little-endian double.
    bits = [n[1].to_f].pack("E").unpack1("Q<")
    [{ "rule" => "fltLit", "bits" => bits }, FLOAT]
  end

  # variables
  def n_var(n)
    kind = n[1]
    name = n[2]
    if kind == "ivar"
      raise Blocked, "read of unset ivar #{name}" unless @ivars.key?(name)

      return [{ "rule" => "ivarRead", "name" => name, "ty" => @ivars[name] }, @ivars[name]]
    end
    raise Blocked, "#{kind} variables are outside the fragment" unless kind == "local"
    raise Blocked, "read of unbound local #{name}" unless @env.key?(name)

    [{ "rule" => "var", "kind" => "lvar", "name" => name }, @env[name]]
  end

  def n_vasgn(n)
    kind = n[1]
    name = n[2]
    d, t = go(n[3])
    if kind == "ivar"
      @ivars[name] = t
      return [{ "rule" => "ivarAsgn", "name" => name, "value" => d }, t]
    end
    raise Blocked, "#{kind} assignment is outside the fragment" unless kind == "local"

    @env[name] = t
    [{ "rule" => "vasgn", "kind" => "lvar", "name" => name, "value" => d }, t]
  end

  def n_const(n) = [{ "rule" => "constCls", "name" => n[1] }, { "tag" => "clsOf", "name" => n[1] }]

  # control
  def n_seq(n)
    ds, ts = go_all(n[1..])
    [{ "rule" => "seq", "stmts" => ds }, ts.empty? ? NIL_T : ts[-1]]
  end

  def n_if(n)
    dc, = go(n[1])
    # Both branches are typed in the incoming environment's *copy*: this emitter
    # does not join environments, so a branch that rebinds a local is a block
    # rather than a guess (`Judge.if'` joins; reproducing that here is not this
    # commit's job).
    before = @env.dup
    dt, tt = go(n[2])
    then_env = @env
    @env = before.dup
    if n[3].nil?
      de = nil
      te = NIL_T
    else
      de, te = go(n[3])
    end
    raise Blocked, "the two branches of an `if` leave different local types" if @env != then_env

    j = join(tt, te)
    [{ "rule" => "if", "cond" => dc, "then" => dt, "else" => de, "join" => j }, j]
  end

  # aggregates
  def n_array(n)
    ds, ts = go_all(n[1])
    # Match elemTy's right fold, including nilable joins.
    elem = ts.reverse.reduce(NEVER) { |acc, t| join(t, acc) }
    [{ "rule" => "arrayLit", "elems" => ds, "elem" => elem }, array_of(elem)]
  end

  def n_hash(n)
    kds = []
    kts = []
    vds = []
    vts = []
    n[1].each do |pair|
      # Exported pairs are [key_ast, value_ast], not tagged nodes.
      unless pair.is_a?(Array) && pair.length == 2 && pair.all? { |e| e.is_a?(Array) }
        raise Blocked, "hash entry '#{pair}' is outside the fragment"
      end

      kd, kt = go(pair[0])
      vd, vt = go(pair[1])
      kds << kd
      kts << kt
      vds << vd
      vts << vt
    end
    k = kts.reverse.reduce(NEVER) { |acc, t| join(t, acc) }
    v = vts.reverse.reduce(NEVER) { |acc, t| join(t, acc) }
    [{ "rule" => "hashLit", "keys" => kds, "vals" => vds, "key" => k, "val" => v },
     hash_of(k, v)]
  end

  # sends
  def n_vcall(n)
    return [{ "rule" => "bareName", "name" => "x" }, { "tag" => "any" }] if n[1] == "x"

    implicit_send(n[1], [])
  end

  def n_send(n)
    recv = n[1]
    m = n[2]
    args = n[3]
    raise Blocked, "a block argument is outside the fragment" unless n[4].nil?
    return implicit_send(m, args) if recv.nil?
    # `C.new(...)`
    return new_inst(recv[1], args) if m == "new" && recv[0] == "const"

    dr, tr = go(recv)
    tr = as_inst(tr)
    dargs, targs = go_all(args)
    ret = prim_ret(tr, m, targs)
    if ret
      return [{ "rule" => "prim", "recv" => dr, "method" => m, "args" => dargs,
                "recvTy" => tr, "retTy" => ret }, ret]
    end
    if tr["tag"] == "inst"
      sig = sig_for(tr["name"], m)
      return [{ "rule" => "callMethodSig", "recv" => dr, "name" => m, "args" => dargs,
                "ret" => sig["ret"] }, sig["ret"]]
    end
    raise Blocked, "no builtin signature for #{tr["tag"]}##{m}/#{targs.length}"
  end

  def implicit_send(m, args)
    dargs, = go_all(args)
    owner = @self_cls || "Object"
    sig = sig_for(owner, m)
    [{ "rule" => "callSig", "name" => m, "args" => dargs, "ret" => sig["ret"] }, sig["ret"]]
  end

  def new_inst(name, args)
    dargs, = go_all(args)
    ivars = @cls_ivars[name]
    raise Blocked, "`#{name}.new` before `class #{name}` is defined" if ivars.nil?

    ty = { "tag" => "inst", "name" => name, "ivars" => spine(ivars) }
    [{ "rule" => "newInst", "cls" => name, "args" => dargs, "ty" => ty }, ty]
  end

  # declarations
  def n_def(n)
    name = n[1]
    params = n[2]
    body = n[3]
    owner = @self_cls || "Object"
    sig = sig_for(owner, name)
    if sig["params"].length != params.length
      raise Blocked, "#{owner}##{name}: sig declares #{sig["params"].length} params, " \
                     "the def has #{params.length}"
    end

    sps = params.each_with_index.map do |p, i|
      unless p[0] == "preq"
        raise Blocked, "#{owner}##{name}: parameter kind '#{p[0]}' is outside the " \
                       "fragment (required positionals only)"
      end

      { "name" => p[1], "ty" => as_inst(sig["params"][i]["ty"]) }
    end

    outer_env = @env
    @env = sps.to_h { |p| [p["name"], p["ty"]] }
    dbody, = go(body)
    @env = outer_env
    [{ "rule" => "defDecl", "name" => name, "params" => sps, "ret" => sig["ret"],
       "body" => dbody }, SYM]
  end

  def n_class(n)
    name = n[1]
    sup = n[2]
    body = n[3]
    raise Blocked, "a computed superclass is outside the fragment" if sup && sup[0] != "const"

    supname = sup&.at(1)
    @supers[name] = supname if supname

    outer_cls = @self_cls
    outer_ivars = @ivars
    outer_env = @env
    @self_cls = name
    @env = {}
    # A subclass starts from its parent's ivars: `class Dog < Animal; end` has
    # `Animal`'s, and `Dog.new("Rex").speak` reads one.
    @ivars = supname ? (@cls_ivars[supname] || []).to_h : {}
    # `initialize` first, so the ivar spine exists before any other method body
    # reads an ivar. One pass, in source order, is not enough for that.
    seed_ivars(name, body)
    dbody, = go(body)
    @ivars = @cls_ivars[supname].to_h if @ivars.empty? && supname && @cls_ivars.key?(supname)
    @cls_ivars[name] = @ivars.to_a
    @self_cls = outer_cls
    @ivars = outer_ivars
    @env = outer_env
    [{ "rule" => "classDecl", "name" => name, "super" => supname, "body" => dbody },
     { "tag" => "clsOf", "name" => name }]
  end

  # The ivar spine of `name`, read off `initialize`'s declared parameters.
  # Only the `@x = <param>` / `@x = <literal>` shapes, which is what the corpus's
  # constructors are. Anything else leaves the ivar unset, and the first read of
  # it blocks -- visible, rather than typed at a guess.
  def seed_ivars(name, body)
    stmts = body[0] == "seq" ? body[1..] : [body]
    stmts.each do |st|
      next unless st[0] == "def" && st[1] == "initialize"

      sig = @sigs[[name, "initialize"]]
      return nil if sig.nil?

      penv = {}
      # Python's `zip` stops at the shorter sequence; Ruby's would pad with nil.
      [st[2].length, sig["params"].length].min.times do |i|
        p = st[2][i]
        penv[p[1]] = sig["params"][i]["ty"] if p[0] == "preq"
      end
      ibody = st[3]
      (ibody[0] == "seq" ? ibody[1..] : [ibody]).each do |s2|
        next unless s2[0] == "vasgn" && s2[1] == "ivar"

        v = s2[3]
        if v[0] == "var" && v[1] == "local" && penv.key?(v[2])
          @ivars[s2[2]] = penv[v[2]]
        elsif v[0] == "int"
          @ivars[s2[2]] = INT
        elsif v[0] == "str"
          @ivars[s2[2]] = STR
        end
      end
    end
    nil
  end
end

# --------------------------------------------------------------------------

def main(argv)
  if argv.include?("--ast")
    ast = JSON.parse(File.read(argv[argv.index("--ast") + 1]))
    sigs = JSON.parse(File.read(argv[argv.index("--sigs") + 1]))
  else
    input = JSON.parse($stdin.read)
    ast = input["ast"].is_a?(Hash) ? input["ast"] : { "ast" => input["ast"] }
    sigs = input["sigs"] || { "sigs" => [], "dropped" => [] }
  end

  em = Emitter.new(sigs)
  begin
    deriv, ty = em.go(ast["ast"])
  rescue Blocked => e
    puts JSON.generate({ "status" => "blocked", "why" => e.message })
    return 0
  rescue SystemStackError
    # The Python original caught RecursionError here; same measurement.
    puts JSON.generate({ "status" => "blocked", "why" => "AST too deep" })
    return 0
  end
  puts JSON.generate({ "status" => "ok", "ty" => ty, "deriv" => deriv })
  0
end

exit(main(ARGV)) if $PROGRAM_NAME == __FILE__
