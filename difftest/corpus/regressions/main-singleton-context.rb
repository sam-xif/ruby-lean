# L283: main singleton context.

# main-include
module Scope1M;def example;3;end;def self.included(c);p c;end;end;p include(Scope1M);p Object.new.example

# main-unsupported-macros
begin;protected;rescue=>e;p [e.class,e.message];end;begin;module_function(:anything);rescue=>e;p [e.class,e.message];end;o=self;begin;o.define_method(:x){1};rescue=>e;p [e.class,e.message];end

# main-reflection
p [respond_to?(:define_method),respond_to?(:define_method,true),respond_to?(:private),respond_to?(:private,true),defined?(define_method)];p [Object.method_defined?(:private),Object.private_method_defined?(:private),Object.new.respond_to?(:private,true)];p [self.to_s,self.inspect];def Object.inspect;:changed;end;p self.inspect
