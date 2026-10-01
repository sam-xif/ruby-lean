module T; UserMarker=11;end
p require('sorbet-runtime')
p [T::UserMarker,T.let(2,Integer)]
