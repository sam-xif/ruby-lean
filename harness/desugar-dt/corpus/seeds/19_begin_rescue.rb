# begin/rescue/else/ensure — evaluation-order trace + exception binding.
# Correct stdout: "body;else;ensure;" then the ZeroDivisionError branch's "0div;".
begin
  print("body;")
rescue => e
  print("rescue;")
else
  print("else;")
ensure
  print("ensure;")
end

# typed rescue with => binding; the FIRST matching clause wins.
begin
  1 / 0
rescue TypeError
  print("type;")
rescue ZeroDivisionError => err
  print("0div=#{err.class.name};")
end

# rescue-modifier: `expr rescue fallback` catches StandardError.
v = (Integer("nope") rescue -1)
print("mod=#{v};")
