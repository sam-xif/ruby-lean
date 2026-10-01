# frozen_string_literal: true

# L282: match forwardable 1.4.0's declarations, aliases and load-time order.
# Its generated source is compiled to RubyCore by __forwardable_compile for
# simple accessors. Other expressions remain an explicit source-compilation gate.
module Forwardable
  VERSION = "1.4.0"
  VERSION.freeze
  FORWARDABLE_VERSION = VERSION
  FORWARDABLE_VERSION.freeze
  @debug = nil
  class << self
    attr_accessor :debug
  end

  def instance_delegate(hash)
    hash.each do |methods, accessor|
      unless defined?(methods.each)
        def_instance_delegator(accessor, methods)
      else
        methods.each { |method| def_instance_delegator(accessor, method) }
      end
    end
  end

  def def_instance_delegators(accessor, *methods)
    methods.each do |method|
      next if /\A__(?:send|id)__\z/ =~ method
      def_instance_delegator(accessor, method)
    end
  end

  def def_instance_delegator(accessor, method, ali = method)
    gen = Forwardable._delegator_method(self, accessor, method, ali)
    mod = Module === self ? self : singleton_class
    mod.module_eval(&gen)
  end

  alias delegate instance_delegate
  alias def_delegators def_instance_delegators
  alias def_delegator def_instance_delegator

  def self._delegator_method(obj, accessor, method, ali)
    accessor = accessor.to_s unless Symbol === accessor
    method_accessor = if Module === obj
      obj.method_defined?(accessor) || obj.private_method_defined?(accessor)
    else
      obj.respond_to?(accessor, true)
    end
    checked = method.match?(/\A[_a-zA-Z]\w*[?!]?\z/)
    __forwardable_compile(accessor, method, ali, method_accessor, checked)
  end
end

module SingleForwardable
  def single_delegate(hash)
    hash.each do |methods, accessor|
      unless defined?(methods.each)
        def_single_delegator(accessor, methods)
      else
        methods.each { |method| def_single_delegator(accessor, method) }
      end
    end
  end

  def def_single_delegators(accessor, *methods)
    methods.each do |method|
      next if /\A__(?:send|id)__\z/ =~ method
      def_single_delegator(accessor, method)
    end
  end

  def def_single_delegator(accessor, method, ali = method)
    gen = Forwardable._delegator_method(self, accessor, method, ali)
    instance_eval(&gen)
  end

  alias delegate single_delegate
  alias def_delegators def_single_delegators
  alias def_delegator def_single_delegator
end
