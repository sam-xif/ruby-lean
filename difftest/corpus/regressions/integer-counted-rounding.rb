# A negative count rounds to a power of ten, and the quotient is floor division,
# so the remainder is never negative. `floor` is that quotient; `ceil` and
# `truncate` step it up (truncate only below zero, where the floor is the
# further-from-zero neighbour); `round` is half **away from zero**, so at the
# halfway point a negative receiver stays on the floor (-195.round(-1) is -200)
# while a positive one steps up (195.round(-1) is 200).

p [-195.round(-1), -195.floor(-1), -195.ceil(-1), -195.truncate(-1)]
p [-204.round(-1), -204.floor(-1), -204.ceil(-1), -204.truncate(-1)]
p [-190.round(-1), -190.floor(-1), -190.ceil(-1), -190.truncate(-1)]
p [-5.round(-1), -5.floor(-1), -5.ceil(-1), -5.truncate(-1)]
p [-10.round(-1), -10.floor(-1), -10.ceil(-1), -10.truncate(-1)]
p [-15.round(-2), -15.floor(-2), -15.ceil(-2), -15.truncate(-2)]
p [-25.round(-2), -25.floor(-2), -25.ceil(-2), -25.truncate(-2)]
p [-95.round(-2), -95.floor(-2), -95.ceil(-2), -95.truncate(-2)]
p [-150.round(-2), -150.floor(-2), -150.ceil(-2), -150.truncate(-2)]
p [-1000005.round(-1), -1000005.floor(-1), -1000005.ceil(-1), -1000005.truncate(-1)]
p [195.round(-1), 195.floor(-1), 195.ceil(-1), 195.truncate(-1)]
p [204.round(-1), 204.floor(-1), 204.ceil(-1), 204.truncate(-1)]
p [-5.round(-100), -5.floor(-100), -5.ceil(-100), -5.truncate(-100)]
p [5.round(-100), 5.floor(-100), 5.ceil(-100), 5.truncate(-100)]
p [-1234567890123456789.round(-18), -1234567890123456789.floor(-18), -1234567890123456789.ceil(-18), -1234567890123456789.truncate(-18)]

# positive counts leave an Integer alone
p [-195.round(1), 195.round(2), -5.truncate(3)]
p [-195.round, 195.floor, -5.ceil, 5.truncate]
