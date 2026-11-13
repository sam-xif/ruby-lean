# A Pathname instance is not the place for a blanket `method_missing`: the
# CRuby name table says which selectors exist, so an invented one raises
# CRuby's `NoMethodError`, a real unmodeled one declines by name, and the
# modeled subset keeps answering. CRuby's Pathname is also not `Comparable`.
def report(label)
  puts "#{label}: #{yield.inspect}"
rescue StandardError => e
  puts "#{label}: #{e.class}: #{e.message}"
end

path = Pathname.new("/a/b.rb")

report("invented") { path.zzz_does_not_exist }
report("not-comparable") { path < Pathname.new("/a/c") }
report("no-between") { path.between?(path, path) }
report("protected-path") { path.path }
report("sent-path") { path.send(:path) }
report("modeled") { [path.to_s, path.basename.to_s, path.dirname.to_s, path.extname] }
report("respond-to") do
  %i[zzz_does_not_exist realpath path basename].map { |name| path.respond_to?(name) }
end
