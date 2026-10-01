p Object.ancestors
[Array,Hash,String,Integer,Float,TrueClass,FalseClass,NilClass,Symbol].each{|c|p c.ancestors}
p JSON.generate({a:[1,true,nil,"x"]})
