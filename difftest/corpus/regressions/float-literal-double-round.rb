# #141: a float literal exports as its IEEE-754 bits, so no decimal-to-binary64
# conversion happens inside the model. The first literal used to decode one ulp
# below CRuby's `strtod`; the second pair is what that ulp costs — two literals
# CRuby distinguishes were one double in the model.
p 403355592039198e57
a = 5.724162270483689e-257
b = 5.7241622704836886e-257
p [a == b, a > b]
p [a, b]
