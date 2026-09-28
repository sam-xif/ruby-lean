class String;def freeze;raise "wrong";end;end;class C;end;p [C.name.frozen?,C.name.equal?(C.name)]
