# frozen_string_literal: true

# Private subprocess for gen_cruby_names.rb. Keep optional library loading out
# of the core oracle snapshot. Marshal avoids requiring a serialization library.
feature = ARGV.fetch(0)
before = Object.constants
require feature
roots = (Object.constants - before).map(&:to_s).sort
seen = {}
visit = lambda do |mod|
  name = mod.name
  return if !name || seen.key?(name)
  seen[name] = [
    (mod.instance_methods(false) + mod.private_instance_methods(false) + mod.protected_instance_methods(false)).map(&:to_s).uniq.sort,
    (mod.singleton_class.instance_methods(false) + mod.singleton_class.private_instance_methods(false) + mod.singleton_class.protected_instance_methods(false)).map(&:to_s).uniq.sort,
    mod.constants(false).map(&:to_s).sort
  ]
  mod.constants(false).each do |n|
    next if mod.autoload?(n)
    value = mod.const_get(n, false)
    visit.call(value) if value.is_a?(Module) && value.name&.start_with?(name + "::")
  end
end
roots.each do |n|
  next if Object.autoload?(n)
  value = Object.const_get(n)
  visit.call(value) if value.is_a?(Module)
end
STDOUT.write(Marshal.dump([roots, seen.sort.to_h]))
