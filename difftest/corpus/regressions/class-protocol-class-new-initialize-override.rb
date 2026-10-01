class Class;alias old_init initialize;def initialize(*a,&b);p [:initialize,a];old_init(*a,&b);end;end;c=Class.new(Array){p :body};p c.superclass
