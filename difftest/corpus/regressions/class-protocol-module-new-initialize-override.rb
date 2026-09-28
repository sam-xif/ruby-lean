class Module;alias old_init initialize;def initialize(*a,&b);p [:initialize,a];old_init(*a,&b);end;end;p Module.new{p :body}.class
