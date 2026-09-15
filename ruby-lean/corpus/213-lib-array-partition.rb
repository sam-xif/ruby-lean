# typed: true
a, b = [1, 2, 3, 4].partition { |x| x.even? }
a.length + b.length
