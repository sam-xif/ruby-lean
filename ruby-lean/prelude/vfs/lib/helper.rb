# frozen_string_literal: true
# A leaf library for the require_relative fixture (issue #7 / M1). No
# dependencies of its own; `greeting.rb` loads it with `require_relative`.
HELPER_CONST = "helper-loaded"

def helper_double(x)
  x * 2
end
