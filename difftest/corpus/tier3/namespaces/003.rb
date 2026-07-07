$g = 10
class Q
  @cv = 100
  @@shared = 5
  def initialize; @iv = 7; end
  def report
    [defined?($g), defined?(@iv), defined?(@@shared), defined?(@nope)]
  end
end
q = Q.new
puts q.report.map { |x| x.inspect }.join(",")
puts $g
puts Q.instance_variable_get(:@cv)
q.report
