add = ->(x) { ->(y) { x + y } }
add.call(1).call(2)
