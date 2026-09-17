# CRuby raises `NoMethodError` — `Module` carries no `new`, unlike `Class`.
# Filed as the M1 (the typing-the-slice milestone plan) tripwire:
# before that fix, a module's eigenclass superclassed `Class`, so `M.new` would
# have resolved through `Class#new` and answered wrongly instead of raising.
# With the fix (eigenclass bottoms at `Module`), this needs no separate
# `Module#new` builtin — the corrected chain simply fails to resolve `new`, same
# as CRuby.
module M
  def self.f = 1
end

begin
  M.new
rescue NoMethodError => e
  puts "#{e.class}: #{e.message}"
end
