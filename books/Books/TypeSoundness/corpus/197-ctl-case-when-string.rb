# typed: true
extend T::Sig
sig { params(t: String).returns(String) }
def kind(t)
  case t
  when "pypi" then "python"
  when "gem" then "ruby"
  else "other"
  end
end

kind("gem") + kind("x")
