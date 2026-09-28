# exception-clone
class ECase0<StandardError;attr_reader :x;def initialize(s);p [:init,s];@x=3;super;end;end;e=ECase0.new("one");f=e.exception("two");p [e.equal?(f),f.class,f.message,f.x,e.exception.equal?(e)]

# exception-object-nil
e=RuntimeError.new("old");p [e.exception.equal?(e),e.exception(e).equal?(e),e.exception(nil).equal?(e),e.exception(nil).message]

# exception-frozen
e=RuntimeError.new("old").freeze;begin;f=e.exception("new");rescue=>err;p [err.class,err.message];end;p [e.message,e.exception.equal?(e),e.exception(e).equal?(e)]

# exception-private-init-clone
class ECase3<StandardError;def initialize(s);p [:init,s];super;end;end;e=ECase3.new("old");p e.exception("new").message

# exception-clone-hooks
class ECase4<StandardError;def initialize_clone(other,**kw);p [:clone,kw];super;end;def initialize_copy(other);p :copy;super;end;end;e=ECase4.new("old");p e.exception("new").message

# copy-freeze-original
class ECase5<StandardError;def initialize_clone(other);other.freeze;super;end;end;e=ECase5.new("old");begin;f=e.exception("new");p [f.message,f.frozen?,e.frozen?];rescue=>x;p [x.class,x.message];end

# copy-freeze-receiver
class ECase6<StandardError;def initialize_clone(other);super;freeze;end;end;e=ECase6.new("old");begin;e.exception("new");rescue=>x;p [x.class,x.message];end;p e.message

# copy-original-frozen-hook
class ECase7<StandardError;def initialize_clone(other);p [frozen?,other.frozen?];super;end;end;e=ECase7.new("old").freeze;begin;e.exception("new");rescue=>x;p [x.class,x.message];end

# copy-raise-hook
class ECase8<StandardError;def initialize_clone(other);raise "hook";end;end;begin;ECase8.new("old").exception("new");rescue=>x;p [x.class,x.message];end

# copy-undef-hook
class ECase9<StandardError;undef initialize_clone;def method_missing(n,*a);p n;end;end;p ECase9.new("old").exception("new").message

nil
