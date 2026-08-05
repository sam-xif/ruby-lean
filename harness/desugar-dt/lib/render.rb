# frozen_string_literal: true

require_relative "rubycore"

# render_core : RubyCore -> Ruby source.
#
# Deliberately over-parenthesized so that the emitted text re-parses to the same
# structure regardless of precedence (implementation-choices.md C2/C9). Output is not
# meant to be pretty — only to be behavior-faithful and re-parseable.
module Render
  module_function

  def core(node)
    raise "not a node: #{node.inspect}" unless node.is_a?(Array)

    case node[0]
    when :int   then node[1].to_s
    when :flt   then node[1].inspect            # finite float literal -> re-parseable
    when :str   then node[1].inspect            # produces a quoted, escaped literal
    when :sym   then ":#{node[1]}"
    when :true  then "true"
    when :false then "false"
    when :nil   then "nil"
    when :self  then "self"
    when :var   then node[2]                    # name already carries its sigil (@ / @@ / $)
    when :vasgn then "(#{node[2]} = #{core(node[3])})"
    when :const then node[1]
    when :casgn then "(#{node[1]} = #{core(node[2])})"
    when :cpath then cpath_str(node[1], node[2])
    when :cpath_asgn then "(#{cpath_str(node[1], node[2])} = #{core(node[3])})"
    when :send  then send_str(node)
    # A vcall renders as the bare identifier — adding `()` would turn it into an
    # fcall and change the dispatch-miss error (NameError vs NoMethodError).
    # Safe to re-parse as a vcall: desugar temps are `__dt_t<N>`-prefixed, so no
    # generated local can shadow a user identifier here.
    when :vcall then node[1]
    when :block then block_str(node)
    when :yield then "yield(#{node[1].map { |a| core(a) }.join(', ')})"
    when :if
      _, c, t, e = node
      # omit else when absent (nil) so the text re-parses to else=nil, not else=[:nil]
      if e
        "(if #{core(c)} then #{core(t)} else #{core(e)} end)"
      else
        "(if #{core(c)} then #{core(t)} end)"
      end
    when :while
      _, c, b = node
      "(while #{core(c)} do #{core(b)} end)"
    when :def
      _, name, params, body = node
      "(def #{name}(#{render_params(params)}); #{core(body)}; end)"
    when :array
      "[" + node[1].map { |n| core(n) }.join(", ") + "]"
    when :hash
      "{" + node[1].map { |k, v| "(#{core(k)}) => (#{core(v)})" }.join(", ") + "}"
    when :splat then node[1] ? "*(#{core(node[1])})" : "*"
    when :fwd   then "..."
    when :kwargs then kwargs_str(node)
    when :return then node[1] ? "return (#{core(node[1])})" : "return"
    when :break  then node[1] ? "break (#{core(node[1])})" : "break"
    when :next   then node[1] ? "next (#{core(node[1])})" : "next"
    when :retry  then "retry"
    when :class
      _, name, sup, body = node
      hdr = sup ? "class #{const_name_str(name)} < (#{core(sup)})" : "class #{const_name_str(name)}"
      "(#{hdr}; #{core(body)}; end)"
    when :module then "(module #{const_name_str(node[1])}; #{core(node[2])}; end)"
    when :sclass then "(class << (#{core(node[1])}); #{core(node[2])}; end)"
    when :defs
      _, recv, name, params, body = node
      "(def (#{core(recv)}).#{name}(#{render_params(params)}); #{core(body)}; end)"
    when :begin  then begin_str(node)
    when :super
      _, args, blk = node
      argstrs = args.map { |a| core(a) }
      argstrs << blockpass_str(blk) if blk && blk[0] == :blockpass
      base = "super(#{argstrs.join(', ')})"
      blk && blk[0] == :block ? "#{base} #{block_str(blk)}" : base
    when :zsuper
      blk = node[1]
      if blk.nil? then "super"
      elsif blk[0] == :blockpass then "super(#{blockpass_str(blk)})"
      else "super #{block_str(blk)}"
      end
    when :defined then "defined?(#{core(node[1])})"
    when :redo  then "redo"
    when :undef then "undef #{node[1].join(', ')}"
    when :alias then "alias #{node[1]} #{node[2]}"
    when :for
      _, targets, coll, body = node
      "(for #{targets.map { |_k, nm| nm }.join(', ')} in (#{core(coll)}); #{core(body)}; end)"
    when :dowhile
      _, body, cond = node
      "(begin; #{core(body)}; end while (#{core(cond)}))"
    when :seq
      "(" + node[1..].map { |n| core(n) }.join("; ") + ")"
    else
      raise "cannot render head :#{node[0]}"
    end
  end

  # (begin; body; rescue E1, E2 => e; h; ...; else; el; ensure; en; end)
  def begin_str(node)
    _, body, rescues, els, ens = node
    s = +"(begin; #{core(body)}"
    rescues.each do |excs, ref, handler|
      s << "; rescue"
      # a splat exc (`rescue *classes`) renders bare (`*(x)`); others are parenthesized.
      s << " " << excs.map { |e| e[0] == :splat ? core(e) : "(#{core(e)})" }.join(", ") unless excs.empty?
      s << " => #{ref[1]}" if ref            # ref[1] carries any sigil (@ / @@ / $)
      s << "; #{core(handler)}"
    end
    s << "; else; #{core(els)}" if els
    s << "; ensure; #{core(ens)}" if ens
    s << "; end)"
    s
  end

  def send_str(node)
    _, recv, mname, args, blk = node
    # A block-pass `&e` is an argument (rendered inside the parens, last); a literal block
    # `{…}` is a trailing brace block. The two are mutually exclusive (rubycore C23/blockpass).
    argstrs = args.map { |a| core(a) }
    argstrs << blockpass_str(blk) if blk && blk[0] == :blockpass
    base =
      if recv
        "(#{core(recv)}).#{mname}(#{argstrs.join(', ')})"
      else
        # nil receiver = implicit-self call; the () keeps it a method call, not a local
        "#{mname}(#{argstrs.join(', ')})"
      end
    blk && blk[0] == :block ? "#{base} #{block_str(blk)}" : base
  end

  # `A::B` (base a node) or `::B` (base nil = top-level). Base is parenthesized so any
  # expression re-parses; `(A)::B` is behavior-identical to `A::B` and valid in definition
  # position too (`class (A)::B`).
  def cpath_str(base, name)
    base ? "(#{core(base)})::#{name}" : "::#{name}"
  end

  # A class/module name is a String (simple constant) or a [:cpath,…] node (`A::B`).
  def const_name_str(name)
    name.is_a?(String) ? name : core(name)
  end

  # `&(e)` block-pass argument, or bare `&` for an anonymous forward.
  def blockpass_str(blk)
    blk[1] ? "&(#{core(blk[1])})" : "&"
  end

  def block_str(node)
    _, params, locals, body = node
    if params.empty? && locals.empty?
      "{ #{core(body)} }"
    else
      bar = render_params(params)
      bar += "; #{locals.join(', ')}" unless locals.empty?
      "{ |#{bar}| #{core(body)} }"
    end
  end

  # Render a structured param list (see RubyCore::PARAM_HEADS) back to Ruby.
  def render_params(params)
    params.map { |p| param_str(p) }.join(", ")
  end

  def param_str(p)
    case p[0]
    when :preq    then p[1]
    when :popt    then "#{p[1]} = (#{core(p[2])})"
    when :prest   then p[1] ? "*#{p[1]}" : "*"
    when :pkey    then p[2] ? "#{p[1]}: (#{core(p[2])})" : "#{p[1]}:"
    when :pkwrest then p[1] ? "**#{p[1]}" : "**"
    when :pblock  then p[1] ? "&#{p[1]}" : "&"
    when :pfwd    then "..."
    when :pdestr  then "(#{render_params(p[1])})"
    else raise "cannot render param :#{p[0]}"
    end
  end

  # Keyword arguments at a call site, rendered *without* braces (bare `k: v` / `**e`) so
  # they re-parse as a keyword hash — NOT a positional hash literal (Ruby-3 separation).
  # Uses `=>` for any key so no valid-label check is needed; `k: v` is sugar for `:k => v`.
  def kwargs_str(node)
    node[1].map do |el|
      if el[0] == :kwsplat
        el[1] ? "**(#{core(el[1])})" : "**"
      else
        "(#{core(el[0])}) => (#{core(el[1])})"
      end
    end.join(", ")
  end
end
