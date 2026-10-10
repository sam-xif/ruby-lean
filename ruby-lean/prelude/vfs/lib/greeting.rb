# frozen_string_literal: true
# Depends on `helper.rb` through a *relative* require, so loading this file
# exercises a transitive require_relative from inside a required file.
require_relative "helper"
GREETING = "hi:" + HELPER_CONST

def greet(n)
  "hello " + n.to_s + " / " + helper_double(n).to_s
end
