# Constant paths (C27): read `A::B` / `::B` / `expr::B`, write `A::B = v`, and constant-
# path names in class/module *definition* position (`class A::B`). Head [:cpath, base, name]
# (base nil = top-level `::B`); assignment [:cpath_asgn, base, name, expr].
module Outer
  Inner = 10
  module Mid
    Deep = 20
  end
end

print("read=#{Outer::Inner};")           # relative path read
print("nested=#{Outer::Mid::Deep};")     # A::B::C

# Reopen a namespaced class via a path name in definition position.
class Outer::Widget
  def kind; "widget"; end
end
print("defpath=#{Outer::Widget.new.kind};")

# Top-level absolute reference.
TOP = 99
print("abs=#{::TOP};")

# Path assignment yields the RHS; eval order is base then RHS.
r = (Outer::Assigned = (print("rhs;"); 42))
print("write=#{r};")
print("readback=#{Outer::Assigned};")

# Non-constant base (an expression that evaluates to a module).
m = Outer
print("exprbase=#{m::Inner};")
Outer::Inner
