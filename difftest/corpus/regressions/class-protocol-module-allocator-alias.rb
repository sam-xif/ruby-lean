class Class;alias make_empty allocate;end;m=Module.make_empty;p [m.class,m.name];p m.send(:initialize){p :body};begin;Module.allocate;rescue=>e;p [e.class,e.message];end
