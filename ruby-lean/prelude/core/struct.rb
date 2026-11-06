# ─── Struct ─────────────────────────────────────────────────────────────────
#
# `Struct.new(:a, :b)` returns a **class**, so the whole feature is a class
# factory: `Class.new` plus `define_method`, both of which the model already has
#. That is the thesis of this project made concrete — a "core class"
# that is really a metaprogramming pattern costs prelude Ruby, not Lean rules.
#
# It could not live here before L103: `inspect`, `to_s` and `==` are part of a
# Struct's contract, and defining any of them in the prelude used to turn off
# pure repr for the whole program.
class Struct
  # `keyword_init: nil` (the default) accepts *either* calling convention, which
  # is what CRuby does for a struct that was not created with an explicit
  # `keyword_init:` [V].
  def self.new(*names, keyword_init: nil, &body)
    return __unsupported__("Struct.new with no members") if names.empty?
    return __unsupported__("Struct.new(\"Name\") (named struct constant)") if names[0].is_a?(String)
    syms = names.map { |n| n.to_sym }
    kwi = keyword_init
    # `Class.new { … }` (block form) is not modeled; `Class.new` + `class_eval`
    # is the same thing and both halves are.
    cls = Class.new
    cls.class_eval do
      define_singleton_method(:members) { syms.dup }

      define_method(:members) { syms.dup }

      define_method(:initialize) do |*a, **kw|
        if kwi == true || (kwi.nil? && a.empty? && !kw.empty?)
          bad = kw.keys.reject { |k| syms.include?(k) }
          raise ArgumentError, "unknown keywords: " + bad.map { |k| k.inspect }.join(", ") unless bad.empty?
          syms.each { |s| instance_variable_set("@" + s.to_s, kw[s]) }
        else
          raise ArgumentError, "struct size differs" if a.length > syms.length
          i = 0
          while i < syms.length
            instance_variable_set("@" + syms[i].to_s, a[i])
            i += 1
          end
        end
        nil
      end

      syms.each do |s|
        define_method(s) { instance_variable_get("@" + s.to_s) }
        define_method(s.to_s + "=") { |v| instance_variable_set("@" + s.to_s, v) }
      end

      define_method(:to_a) { syms.map { |s| send(s) } }
      define_method(:deconstruct) { syms.map { |s| send(s) } }

      define_method(:to_h) do
        h = {}
        syms.each { |s| h[s] = send(s) }
        h
      end

      define_method(:[]) do |k|
        if k.is_a?(Integer)
          i = k < 0 ? syms.length + k : k
          raise IndexError, "offset " + k.to_s + " too large for struct(size:" + syms.length.to_s + ")" if i < 0 || i >= syms.length
          send(syms[i])
        else
          key = k.to_sym
          raise NameError, "no member '" + k.to_s + "' in struct" unless syms.include?(key)
          send(key)
        end
      end

      define_method(:==) do |other|
        other.class == self.class && syms.all? { |s| send(s) == other.send(s) }
      end

      define_method(:eql?) { |other| self == other }

      define_method(:each) do |&blk|
        return __unsupported__("Enumerator: Struct#each without a block") if blk.nil?
        syms.each { |s| blk.call(send(s)) }
        self
      end

      define_method(:size) { syms.length }
      define_method(:length) { syms.length }

      define_method(:inspect) do
        parts = syms.map { |s| s.to_s + "=" + send(s).inspect }
        nm = self.class.name
        "#<struct " + (nm.nil? ? "" : nm + " ") + parts.join(", ") + ">"
      end

      define_method(:to_s) { inspect }
    end
    cls.class_eval(&body) unless body.nil?
    cls
  end
end

# Module's constructor allocates internally; its public allocate name is undefined.
class << Module
  undef_method :allocate
end
