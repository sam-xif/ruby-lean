# L277: frozen-error and final-result inspection dispatch user methods.
class Plain; end

o = Plain.new
def o.inspect = "SING"
o.freeze
begin
  o.instance_variable_set(:@x, 1)
rescue StandardError => e
  puts("frozen, impure receiver => #{e.class}: #{e.message}")
end

a = [1]
def a.inspect = "SING"
a.freeze
begin
  a.push(2)
rescue StandardError => e
  puts("frozen, impure array => #{e.class}: #{e.message}")
end

# and the observation: the value this program *returns* is the impure object, so
# `result_repr` has to render it without a machine to dispatch in
r = Plain.new
def r.inspect = "SING"
r
