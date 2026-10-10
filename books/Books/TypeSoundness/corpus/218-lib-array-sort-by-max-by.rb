# typed: true
xs = ["bbb", "a", "cc"]
xs.sort_by { |s| s.length }.first + xs.max_by { |s| s.length }
