# L283: frozen declaration scope.

# frozen-lexical-class
module Scope1M;freeze;begin;class Scope1C;end;rescue=>e;p [e.class,e.message];end;end;p Scope1M.const_defined?(:Scope1C,false)

# frozen-qualified-class
module Scope2M;freeze;end;begin;class Scope2M::Scope2C;end;rescue=>e;p [e.class,e.message];end;p Scope2M.const_defined?(:Scope2C,false)

# frozen-eval-lexical
class Scope3C;end;Scope3C.freeze;Scope3C.class_eval{Scope3X=1;class Scope3Nested;end};p [Scope3X,Scope3Nested.name,Scope3C.const_defined?(:Scope3X,false)]

# frozen-reopen-existing
module Scope4M;class Scope4C;end;freeze;end;class Scope4M::Scope4C;def x;1;end;end;p Scope4M::Scope4C.new.x
