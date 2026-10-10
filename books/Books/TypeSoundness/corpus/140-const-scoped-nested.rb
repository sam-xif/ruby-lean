# typed: true
module Outer
  module Inner
    Y = "deep"
  end
end

Outer::Inner::Y
