#!/usr/bin/env ruby
# frozen_string_literal: true

# The theorems in this book are about the model. This asks whether the model
# and CRuby agree on this program. `make book-checks` runs it.
exec(File.join(__dir__, "../../../bin/ruby-lean"), "--compare", File.join(__dir__, "loop_sum.rb"))
