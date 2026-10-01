# proc-init-copy
original=proc{1};q=Proc.new(&original);p [q.equal?(original),q.call,q.lambda?]

# proc-copy
original=proc{1};q=Proc.new(&original);p [q.equal?(original),q.call,q.lambda?];l=lambda{2};q=Proc.new(&l);p [q.equal?(l),q.call,q.lambda?]

# proc-subclass
class CPart2<Proc;def initialize(*a);p a;end;end;original=proc{1};q=CPart2.new(3,&original);p [q.class,q.equal?(original),q.call]

# proc-args
begin;Proc.new(1){2};rescue=>e;p [e.class,e.message];end

# proc-no-block
begin;Proc.new;rescue=>e;p [e.class,e.message];end

# proc-new-no-block-custom
class Proc;def initialize;p :init;end;end;begin;Proc.new;rescue=>e;p [e.class,e.message];end

# proc-user-init
class Proc;def initialize(*a,&b);p [a,block_given?];end;end;p Proc.new(2){3}.call

nil
