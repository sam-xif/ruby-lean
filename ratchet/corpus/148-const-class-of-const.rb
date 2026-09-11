# typed: true
module M
  class Box
  end
end

M::Box.new.class.to_s
