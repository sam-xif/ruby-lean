# initialize-block
class CPart0;attr_reader :x;def initialize(x,k:,&b);@x=[x,k,b.call];end;end;p CPart0.new(1,k:2){3}.x

# hash-init-block
h=Hash.new{|h,k|h[k]=k.to_s};p h[:a];p h

# hash-sub-init-block
class CPart2<Hash;end;h=CPart2.new{|h,k|h[k]=k.to_s};p [h.class,h[:a]]

# array-init-block
p Array.new(3){|i|i*2}

# hash-block-args
begin;Hash.new(1){2};rescue=>e;p [e.class,e.message];end

# array-init-reentrant
class CPart5<Array;def initialize;super(3){|i|p dup;self << 7;i};end;end;p CPart5.new

# array-init-frozen-block
a=[];begin;a.send(:initialize,2){|i|a.freeze;i};rescue=>e;p [e.class,e.message];end;p a

# hash-default-lambda
[lambda{},lambda{|a|},lambda{|a,b,c|},lambda{|a,*b|},lambda{|a,b,c,*d|}].each{|b|begin;Hash.new(&b);p :ok;rescue=>e;p [e.class,e.message];end};nil

nil
