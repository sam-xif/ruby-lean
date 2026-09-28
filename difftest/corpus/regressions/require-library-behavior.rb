require 'forwardable'
class Wrap;extend Forwardable;def_delegators :@list,:size,:first;def initialize;@list=[1,2];end;end
p [Wrap.new.size,Wrap.new.first]

p require("uri");p URI.decode_www_form_component("a+b%20c")
