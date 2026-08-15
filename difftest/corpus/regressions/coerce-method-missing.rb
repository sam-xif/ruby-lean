# L123. `Integer + obj` must call a `method_missing`-supplied `coerce`: CRuby's
# `rb_check_funcall` takes one, so the body *runs* (printing "in mm") and the
# failure is about the shape it returned, not about the class chain.
class C
  def method_missing(name, *args)
    puts("in mm: #{name} #{args.inspect}")
    "mm-#{name}"
  end

  def inspect = "#<C>"
end

["+", "-", "*", "/", "%", "**"].each do |op|
  begin
    puts(0.send(op, C.new).inspect)
  rescue StandardError => e
    puts("#{op} #{e.class}: #{e.message}")
  end
end
["<", ">", "<=", ">=", "<=>"].each do |op|
  begin
    puts(0.send(op, C.new).inspect)
  rescue StandardError => e
    puts("#{op} #{e.class}: #{e.message}")
  end
end
puts((0 == C.new).inspect)
puts("end")
