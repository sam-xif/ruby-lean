# forward-single-frozen
module SingleForwardable;end;SingleForwardable.freeze;begin;require 'forwardable';rescue=>e;p [e.class,e.message];end;p Forwardable::VERSION
