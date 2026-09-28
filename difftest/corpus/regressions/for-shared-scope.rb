# L288: for shared scope.

# for-empty-declare
p defined?(x);for x in [];y=1;end;p [defined?(x),defined?(y),x,y]

# for-new-locals
for x in [1];new_local=7;end;p [x,new_local];for y in [];skipped=1;end;p [y,skipped]

# for-loop-scope
x=1;f=proc{x};for x in [2,3];y=x;end;p [x,y,f.call]

# for-captured-vars
fs=[];for x in [1,2,3];y=x;fs<<proc{[x,y]};end;p fs.map{|f|f.call};p [x,y]

# for-nested
for x in [1,2];for y in [3,4];z=x+y;p z;end;end;p [x,y,z]

# for-nested-captured-block
x=99;a=[1].map{|v|for x in [2,3];y=x+v;end;proc{[x,y,v]}};p a[0].call;p x

# for-body-environment
def f;for x in [1];p [block_given?,yield(x)];end;end;f{|x|x+1}

# for-match-scope
/x(.)/=~"xa";for x in [1];/y(.)/=~"yb";p $1;end;p $1

# for-nested-capture
x=99;class EForCase8;def each(&b);$b=b;end;end;[1].each{|z|for x in EForCase8.new;y=z;end;p defined?(y)};p x;p $b.call(7);p x

nil
