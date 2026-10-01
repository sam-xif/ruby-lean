# forward-retry
module Forwardable
 def self.method_added(n)
 if !@stopped && n==:def_instance_delegator
 @stopped=true;raise 'stop loading'
 end
 end
end
begin;require 'forwardable';rescue=>e;p e.message;end
p Forwardable.method_defined?(:def_instance_delegator)
p require('forwardable')
p require('forwardable')
