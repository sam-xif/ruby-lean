# forward-recursive
module Forwardable
 def self.method_added(n);p require('forwardable') if n==:def_delegator;end
end
p require('forwardable')
