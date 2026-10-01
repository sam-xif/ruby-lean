# L282: alias super context.

# alias-super-parent
module Case0
  class ASBase;def foo;[:A];end;def bar;[:wrong];end;end
  class ASParent<ASBase;def foo;p defined?(super);super+[:B];end;end
  class ASChild<ASParent;alias bar foo;end
  p ASChild.new.bar
end

# alias-super-module
module Case1
  class AMParent;def foo;[:P];end;end
  module AMModule;def foo;super+[:M];end;alias bar foo;end
  class AMChild<AMParent;include AMModule;end
  p AMChild.new.bar
end

# alias-super-repeat
module Case2
  module ASTerm;def foo;:first;end;end
  module ASOther;def foo;:second;end;end
  module ASForward;def foo;[:forward,super];end;end
  class ASB;include ASOther;end
  class ASA<ASB;include ASTerm;include ASForward;end
  class ASB;include ASForward;alias bar foo;end
  p ASA.new.bar
  class ASA;alias baz bar;end
  p ASA.new.baz
end
