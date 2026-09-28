p [defined?(T),defined?(URI),defined?(Forwardable)]
p [Object.const_defined?(:T),Object.const_defined?(:URI),Object.const_defined?(:Forwardable)]
[:T,:URI,:Forwardable].each { |n| begin; Object.const_get(n);rescue NameError=>e;p e.class;end }

module T;end;module URI;end;module Forwardable;end;p [T.respond_to?(:coerce),URI.const_defined?(:VERSION),Forwardable.method_defined?(:def_instance_delegator)];begin;T::Configuration;rescue NameError=>e;p e.class;end
