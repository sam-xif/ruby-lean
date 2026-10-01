module Forwardable
  def self.method_added(name)
    p name
  end
end
require 'forwardable'
