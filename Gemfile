# Ruby dependencies for the whole repo: the desugarer (`desugar/`), the typed
# pipeline's Sorbet stage (`ruby-lean/scripts/`) and the strip chain
# (`difftest/ruby/`). `make deps` installs exactly what Gemfile.lock pins.
#
# Sorbet is pinned exactly because its verdict decides which programs reach the
# validator: a Sorbet bump can move the gate's numbers without any change here.
source "https://rubygems.org"

ruby "~> 4.0.0"

gem "prism", "1.8.1"            # the parser under desugar/ (a default gem of Ruby 4.0)
gem "sorbet", "0.6.13405"
gem "sorbet-runtime", "0.6.13405"
