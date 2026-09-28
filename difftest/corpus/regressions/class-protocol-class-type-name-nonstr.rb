class NilClass;def self.to_s;7;end;end;begin;Class.new(nil);rescue=>e;p [e.class,e.message];end
