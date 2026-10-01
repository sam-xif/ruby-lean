# initialize-return-string
class CPart0<String;def initialize;p super('abc');end;end;c=CPart0.new;p [c.class,c]

# initialize-return-array
class CPart1<Array;def initialize;p super(2,3);end;end;c=CPart1.new;p [c.class,c]

# initialize-return-hash
class CPart2<Hash;def initialize;p super(5);end;end;c=CPart2.new;p [c.class,c[:x]]

# initialize-return-exception
class CPart3<StandardError;def initialize;p super('msg');end;end;c=CPart3.new;p [c.class,c.message]

# initialize-undef-string
class CPart4<String;undef initialize;def method_missing(n,*a);p [n,a];end;end;c=CPart4.new('abc');p [c.class,c]

# initialize-undef-array
class CPart5<Array;undef initialize;def method_missing(n,*a);p [n,a];end;end;c=CPart5.new(3);p [c.class,c]

# initialize-undef-hash
class CPart6<Hash;undef initialize;def method_missing(n,*a);p [n,a];end;end;c=CPart6.new(3);p [c.class,c[:x]]

# initialize-undef-exception
class CPart7<StandardError;undef initialize;def method_missing(n,*a);p [n,a];end;end;c=CPart7.new('msg');p [c.class,c.message]

# initialize-native-arity
[Object,BasicObject].each{|c|begin;c.new(1);rescue=>e;p [e.class,e.message];end};p BasicObject.new.__send__(:initialize)

# string-init-preserve
s="abc";p [s.send(:initialize),s];s.freeze;p s.send(:initialize);begin;s.send(:initialize,"a");rescue=>e;p [e.class,e.message];end

# hash-reinit-no-writer
h=Hash.new(2);h[:a]=1;p h.send(:initialize);p [h,h[:x]];h.send(:initialize,3);p [h,h[:x]];h.send(:initialize){|h,k|k};p [h,h[:x]]

# core-init-alias
class CPart11<Array;alias fill initialize;public :fill;end;c=CPart11.allocate;p [c.fill(2){|i|i},c]

# init-frozen
["abc".freeze,[1].freeze,{a:1}.freeze,RuntimeError.new("x").freeze].each{|v|begin;p v.send(:initialize);rescue=>e;p [e.class,e.message];end}

# initializer-error-order
["abc".freeze,[].freeze,{}.freeze,RuntimeError.new("x").freeze].each{|v|begin;v.send(:initialize,1,2,3);rescue=>e;p [e.class,e.message];end};h={}.freeze;begin;h.send(:initialize,1){2};rescue=>e;p [e.class,e.message];end

nil
