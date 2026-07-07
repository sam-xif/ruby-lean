module X; def m; "X" + (defined?(super) ? super : ""); end; end
module Y; def m; "Y" + (defined?(super) ? super : ""); end; end
class E
  include X
  include Y
  def m; "E" + (defined?(super) ? super : ""); end
end
puts E.new.m
puts E.ancestors.select { |a| [E, X, Y].include?(a) }.map(&:to_s).join(",")
