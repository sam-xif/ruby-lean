xs = [1, 2, 3]
[xs.any? { |x| x > 2 }, xs.all? { |x| x > 0 }, xs.include?(2), xs.empty?].length
