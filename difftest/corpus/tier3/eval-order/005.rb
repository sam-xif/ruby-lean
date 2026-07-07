$o = []
def arr
  $o << "arr"
  $store
end
def idx
  $o << "idx"
  0
end
$store = [10]
arr[idx] += ($o << "rhs"; 5)
p $store
p $o
