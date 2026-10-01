# L282: method mutation frozen.

# frozen-alias_method(:b,:a)
module Case0
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { alias_method(:b,:a) };rescue=>e;p [e.class,e.message];end
end

# frozen-remove_method(:a)
module Case1
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { remove_method(:a) };rescue=>e;p [e.class,e.message];end
end

# frozen-undef_method(:a)
module Case2
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { undef_method(:a) };rescue=>e;p [e.class,e.message];end
end

# frozen-attr_accessor(:x)
module Case3
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { attr_accessor(:x) };rescue=>e;p [e.class,e.message];end
end

# frozen-private(:a)
module Case4
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { private(:a) };rescue=>e;p [e.class,e.message];end
end

# frozen-include(Enumerable)
module Case5
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { include(Enumerable) };rescue=>e;p [e.class,e.message];end
end

# frozen-prepend(Enumerable)
module Case6
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { prepend(Enumerable) };rescue=>e;p [e.class,e.message];end
end

# frozen-extend(Enumerable)
module Case7
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { extend(Enumerable) };rescue=>e;p [e.class,e.message];end
end

# frozen-define_method(:x){2}
module Case8
  class C;def a;1;end;end;C.freeze
  begin;C.class_eval { define_method(:x){2} };rescue=>e;p [e.class,e.message];end
end
