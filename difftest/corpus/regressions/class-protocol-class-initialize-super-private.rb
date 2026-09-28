class Class;alias saved_initialize initialize;def initialize(*args);p :before;v=saved_initialize(*args);p [v.equal?(self),superclass];v;end;private :initialize;end;p Class.new(Array).new.class
