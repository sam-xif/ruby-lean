# break-yield
class CPart0;def initialize;begin;p yield;p :after;ensure;p :ensure;end;end;end;p(CPart0.new{break 7})

# break-call
class CPart1;def initialize(&b);p b.call;p :after;end;end;p(CPart1.new{break 7})

# break-helper
class CPart2;def helper;yield;p :helper_after;end;def initialize(&b);helper(&b);p :init_after;end;end;p(CPart2.new{break 7})

# init-return
class CPart3;def initialize;return 7;end;end;p CPart3.new.class

# class-break
p(Class.new{break 7});p(Module.new{break 8})

# array-block-break
p(Array.new(3){|i| break 7 if i==1;i});p Array.new(3){|i|next i+2}

# proc-detached-break
b=proc{break 7};def run(&b);b.call;end;begin;p run(&b);rescue=>e;p [e.class,e.message];end

# forward-break
def inner;yield;p :inner;end;def outer(&b);inner(&b);p :outer;end;p(outer{break 7})

# forward-break-ensure
def inner;yield;ensure;p :inner;end;def outer(&b);inner(&b);ensure;p :outer;end;p(outer{break 7})

# constructor-return
class CPart9;def initialize;yield;p :after;ensure;p :init_ensure;end;end;def run;CPart9.new{return 7};:unreachable;ensure;p :run_ensure;end;p run

# constructor-redo-next
class CPart10;attr_reader :x;def initialize;@x=yield;end;end;i=0;c=CPart10.new{i+=1;redo if i<2;next 7};p [c.x,i]

# constructor-raise
class CPart11;def initialize;yield;ensure;p :ensure;end;end;begin;CPart11.new{raise "bad"};rescue=>e;p [e.class,e.message];end

# constructor-break-super-implicit
class CPart12;def initialize;yield;end;def self.new;super;p :after;end;end;p(CPart12.new{break 7})

# super-literal-break
class ParentPart13;def x;yield;p :unreachable;end;end;class ChildPart13<ParentPart13;def x;p(super(){break 7});p :after;end;end;ChildPart13.new.x

nil
