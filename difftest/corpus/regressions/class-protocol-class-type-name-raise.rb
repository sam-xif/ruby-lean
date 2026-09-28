class Integer;def self.to_s;p :effect;raise "stop";end;end;begin;Class.new(1);rescue=>e;p [e.class,e.message];end
