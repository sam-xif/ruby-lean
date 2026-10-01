# L278: exact Float expansion and IEEE rounding without numerator/denominator overflow.
p [0.1.to_r, (-1.2).to_r, 1.5.to_r, (-0.0).to_r]
p [Rational(10 ** 400, 10 ** 399).to_f, Rational(10 ** 400, 3).to_f]
p [Rational(1, 2 ** 1074).to_f, Rational(-1, 2 ** 1074).to_f]
p [Rational(1, 2 ** 1075).to_f, Rational(-1, 2 ** 1075).to_f]
p [Rational(3, 2 ** 1075).to_f, Rational(5, 2 ** 1075).to_f]
p [Rational(2 ** 53 + 1, 2 ** 53).to_f, Rational(2 ** 53 + 3, 2 ** 53).to_f]
p Rational(2 ** 53 - 1, 2 ** 1075).to_f
p [Rational(1, 10).to_f, Rational(-1, 10).to_f]
p [(1.2.to_r).to_f == 1.2, (Rational(1, 2 ** 1074).to_f).to_r]
# CRuby's Bignum/Fixnum path rounds the operands before division.
p Rational(74993924844200426125206210008109106712806312011710, 68506977879177931).to_f
