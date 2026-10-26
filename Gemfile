# frozen_string_literal: true

# Ruby dependencies for the whole repo: the desugarer (`desugar/`), the typed
# pipeline's Sorbet stage (`ruby-lean/scripts/`) and the strip chain
# (`difftest/ruby/`). `make deps` installs exactly what Gemfile.lock pins.
#
# Sorbet is pinned exactly because its verdict decides which programs reach the
# validator: a Sorbet bump can move the gate's numbers without any change here.
source "https://rubygems.org"

ruby "~> 4.0.0"

gem "prism", "1.8.1" # the parser under desugar/ (a default gem of Ruby 4.0)
gem "sorbet", "0.6.13405"
gem "sorbet-runtime", "0.6.13405"

# The checks on the tooling itself (`make lint`, `make ruby-unit`).
#
# RuboCop needs `json`. It is pinned to the version Ruby 4.0.5 ships as a default
# gem: the generators run outside Bundler, so a newer `json` installed here would
# be the one they load, and `gen_cruby_names.rb` records JSON's own methods.
group :development do
  gem "json", "2.18.0"
  gem "minitest", "6.0.6"
  gem "rubocop", "1.92.0"
  gem "simplecov", "1.3.2"
end
