# typed: true
m = "1.2.3".match(/(\d+)\.(\d+)/)
m[1] + "-" + m[2]
