class StopIteration;alias __l286_saved_initialize initialize;end
# stop
$n=nil
class StopIteration;def initialize(*a);p [:init,a,$!.class,result];super;end;end;e=[].each;2.times{begin;e.next;rescue=>x;p [x.class,x.message,x.result];end}
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-fiber-context
$n=nil
class StopIteration;def initialize(s);p [:init,$!.class,result];super;end;end;begin;1/0;rescue;e=[].each;2.times{begin;e.next;rescue=>x;p [x.message,x.result];end};end
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-live-message
$n=nil
class StopIteration;def initialize(s);p [:init,s];super;end;end;e=[].each;begin;e.next;rescue=>x;x.message << "!";end;begin;e.next;rescue=>y;p [y.message,y.message.equal?(x.message),y.result];end
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-init-fails
$n=nil
class StopIteration;def initialize(s);$n=($n||0)+1;raise "first" if $n==1;super;end;end;e=[].each;2.times{begin;e.next;rescue=>x;p [x.class,x.message];end}
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-no-super
$n=nil
class StopIteration;def initialize(s);p [:init,s];end;end;e=[].each;2.times{begin;e.next;rescue=>x;p [x.class,x.message];end}
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-freeze-first
$n=nil
class StopIteration;def initialize(s);$n=($n||0)+1;super;freeze if $n==1;end;end;e=[].each;2.times{begin;e.next;rescue=>x;p [x.class,x.message];end}
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-mutated-result
$n=nil
e=[1].each;e.next;begin;e.next;rescue=>x;x.result<<2;end;begin;e.next;rescue=>y;p y.result;end

# stop-rewind
$n=nil
class StopIteration;def initialize(s);p :init;super;end;end;e=[].each;begin;e.next;rescue;end;e.rewind;begin;e.next;rescue=>x;p x.message;end
class StopIteration;alias initialize __l286_saved_initialize;end
# stop-nil-conversion
$n=nil
class StopIteration;def initialize(s);p [:init,s];end;end;class NilClass;def to_str;p :convert;"converted";end;end;e=[].each;2.times{begin;e.next;rescue=>x;p [x.class,x.message];end}
class StopIteration;alias initialize __l286_saved_initialize;end
nil
