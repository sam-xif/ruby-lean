puts "clone-hash-default-sharing"
begin
  h=Hash.new([]);
  h[:a]=[1];
  c=h.clone;
  p [c[:absent].equal?(h[:absent]),c[:a].equal?(h[:a])];
  c[:b]=2;
  p [h,c]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-hash-default-proc"
begin
  h=Hash.new{|s,k|p s.class;
  k.to_s};
  c=h.clone(freeze:false);
  p [h[:a],c[:b]]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-enum-started"
begin
  e=[1,2].each;
  e.next;
  begin;
  e.clone(freeze:false);
  rescue=>x;
  p [x.class,x.message];
  end
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-enum-unstarted"
begin
  e=[1,2].each;
  c=e.clone(freeze:false);
  p [c.next,e.next,c.next,e.next]
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-range-regexp-enum-explicit-freeze"
begin
  [1..2,Regexp.new("x").freeze,[1].each].each{|o|[nil,false,true].each{|f|c=o.clone(freeze:f);
  p [c,c.class,c.frozen?,c.equal?(o)]}}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

puts "clone-regexp-new"
begin
  s=Regexp.new("x");
  [nil,false,true].each{|f|c=s.clone(freeze:f);
  p [c,c.frozen?,s.frozen?]}
rescue Exception => __l298_error
  p [:caught, __l298_error.class, __l298_error.message]
end

nil
