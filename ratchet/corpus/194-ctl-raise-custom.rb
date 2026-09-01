class Uncomparable < StandardError
end

def cmp(a)
  raise Uncomparable if a.nil?
  1
rescue Uncomparable
  0
end

cmp(nil) + cmp(1)
