def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end
class MissingHandler
  def method_missing(name, *args, &block)
    return [name, args, block.call] if name == :handled
    super
  end
  def bare = absent
  def parens = absent()
  def parent = super
  private
  def secret = :secret
  protected
  def guarded = :guarded
end
h = MissingHandler.new
show(:handled) { h.handled(1) { 2 } }
show(:bare) { h.bare }
show(:parens) { h.parens }
show(:super) { h.parent }
show(:private) { h.secret }
show(:protected) { h.guarded }
show(:no_name) { Object.new.send(:method_missing) }
show(:wrong_name) { Object.new.send(:method_missing, "x") }
# Nested missing calls overwrite the execution-context reason.
class NestedMissing
  def method_missing(name, *args)
    if name == :absent
      begin
        Object.new.other
      rescue NoMethodError
      end
    end
    super
  end
  def bare = absent
end
show(:nested_reason) { NestedMissing.new.bare }
class SuperHandler
  def method_missing(name, *args) = [name, args]
  def parent(x) = super
end
show(:super_handler) { SuperHandler.new.parent(3) }
class NativeAlias
  alias missing method_missing
end
show(:native_alias) { NativeAlias.new.send(:missing, :gone) }
class UndefMissing
  undef method_missing
end
show(:undef) { UndefMissing.new.gone }
