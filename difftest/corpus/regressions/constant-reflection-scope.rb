module ReflectionBase
  X = 3
end
module ReflectionChild
  include ReflectionBase
end
class ReflectionParent
  X = 5
end
class ReflectionClass < ReflectionParent
end
[ReflectionChild, ReflectionClass].each do |scope|
  p [scope.const_defined?(:X), scope.const_defined?(:X, false)]
  p scope.const_get(:X)
  begin
    scope.const_get(:X, false)
  rescue NameError => e
    p e.message
  end
end
p [ReflectionChild.const_defined?(:Object), ReflectionChild.const_defined?(:Object, false)]
p ReflectionChild.const_get(:Object)
[Object, ReflectionChild].each do |scope|
  begin
    scope.const_get(:NotDefinedInThisProgram)
  rescue NameError => e
    p e.message
  end
end
begin
  Object.const_defined?
rescue ArgumentError => e
  p e.message
end
begin
  Object.const_get(:Object, true, false)
rescue ArgumentError => e
  p e.message
end
