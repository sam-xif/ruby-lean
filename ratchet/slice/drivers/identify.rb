# Driver for `vulns/identify.rb` — the OSV query-key derivation: given a formula
# source URL, which forge repository is it, which release tag, and which package
# registry (with a purl) does it come from.
#
# The file is a table of regexes and a `case/when` over them, so the driver is a
# table of URLs: one per branch that the file can take, plus the near-misses that
# have to *not* match. A `Purl` and a `RegistryPackage` both carry an address in
# their default `inspect`, so every observation renders through `to_s` or a field
# (N38: process-independent output).

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

I = Homebrew::Vulns::Identify

puts("== repo_url: the forge, from any of the URLs a formula carries")
[
  "https://github.com/Example/LibExample/archive/refs/tags/v1.4.2.tar.gz",
  "https://codeberg.org/Example/LibExample/archive/v1.4.2.tar.gz",
  "https://gitlab.com/example/libexample/-/archive/1.4.2/libexample-1.4.2.tar.gz",
  "https://gitlab.gnome.org/GNOME/glib/-/archive/2.80.0/glib-2.80.0.tar.gz",
  "https://gitlab.freedesktop.org/xorg/lib/libx11/-/archive/1.8/libx11-1.8.tar.gz",
  "https://invent.kde.org/frameworks/kconfig.git",
  "https://web.archive.org/web/20200101000000/https://github.com/example/libexample/archive/v1.0.tar.gz",
  "https://gitlab.com/-/snippets/1",          # a host-level route, rejected
  "https://gitlab.com/api/v4/projects/1",     # ditto
  "https://example.test/tarballs/libexample-1.4.2.tar.gz",
].each { |u| show("  #{u}") { I.repo_url(u) } }
show("  several urls, first match wins") do
  I.repo_url(nil, "https://example.test/x.tar.gz", "https://github.com/a/b/archive/v1.tar.gz")
end
show("  no urls") { I.repo_url }

puts
puts("== tag: the release tag, by the six patterns that name one")
[
  "https://github.com/example/libexample/archive/refs/tags/v1.4.2.tar.gz",
  "https://github.com/example/libexample/archive/refs/tags/v1.4.2.zip",
  "https://github.com/example/libexample/archive/1.4.2.tar.gz",
  "https://github.com/example/libexample/archive/1.4.2.zip",
  "https://github.com/example/libexample/releases/download/v1.4.2/libexample.tar.gz",
  "https://github.com/example/libexample/tarball/v1.4.2",
  "https://example.test/libexample-1.4.2.tar.gz",
  nil,
].each { |u| show("  #{u.inspect}") { I.tag(u) } }

puts
puts("== registry_purl: the package registry, and the purl for it")
[
  "https://files.pythonhosted.org/packages/source/r/requests/requests-2.31.0.tar.gz",
  "https://registry.npmjs.org/lodash/-/lodash-4.17.21.tgz",
  "https://registry.npmjs.org/@babel/core/-/core-7.24.0.tgz",
  "https://static.crates.io/crates/ripgrep/ripgrep-14.1.0.crate",
  "https://rubygems.org/downloads/nokogiri-1.16.0.gem",
  "https://rubygems.org/downloads/nokogiri-1.16.0-arm64-darwin.gem",
  "https://hackage.haskell.org/package/pandoc-3.1.11/pandoc-3.1.11.tar.gz",
  "https://repo.hex.pm/tarballs/phoenix-1.7.10.tar",
  "https://cpan.metacpan.org/authors/id/M/MS/MSHELOR/Digest-SHA-6.04.tar.gz",
  "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-core/2.14.1/log4j-core-2.14.1.jar",
  "https://cran.r-project.org/src/contrib/jsonlite_1.8.8.tar.gz",
  "https://api.nuget.org/v3-flatcontainer/newtonsoft.json/13.0.3/newtonsoft.json.13.0.3.nupkg",
  "https://example.test/tarballs/libexample-1.4.2.tar.gz",
  "https://files.pythonhosted.org/packages/py3/r/requests/requests-2.31.0-py3-none-any.whl",
].each do |u|
  show("  #{u}") do
    reg = I.registry_purl(u)
    reg.nil? ? nil : [reg[0], reg[1].to_s]
  end
end

puts
puts("== registry_package: the OSV-facing name, per ecosystem's own rule")
[
  "https://files.pythonhosted.org/packages/source/z/zope.interface/zope.interface-6.1.tar.gz",
  "https://registry.npmjs.org/@babel/core/-/core-7.24.0.tgz",
  "https://cpan.metacpan.org/authors/id/M/MS/MSHELOR/Digest-SHA-6.04.tar.gz",
  "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-core/2.14.1/log4j-core-2.14.1.jar",
  "https://rubygems.org/downloads/nokogiri-1.16.0.gem",
  nil,
].each do |u|
  show("  #{u.inspect}") do
    pkg = I.registry_package(u)
    pkg.nil? ? nil : [pkg.ecosystem, pkg.name, pkg.version, pkg.purl]
  end
end

puts
puts("== the helpers the table leans on")
show("decode plain")     { I.decode("lodash-4.17.21") }
show("decode percent")   { I.decode("%40babel%2Fcore") }
show("decode malformed") { I.decode("100%") }
show("version_after_prefix hit")  { I.version_after_prefix("lodash-4.17.21", "lodash") }
show("version_after_prefix miss") { I.version_after_prefix("lodash-4.17.21", "underscore") }
show("gem_name_version")          { I.gem_name_version("nokogiri-1.16.0-arm64-darwin-22") }
show("gem_name_version no ver")   { I.gem_name_version("nokogiri") }
