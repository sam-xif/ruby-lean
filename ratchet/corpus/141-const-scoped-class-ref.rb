# typed: true
module M
  class Box
    def initialize(v)
      @v = v
    end

    def get
      @v
    end
  end
end

M::Box.new(7).get
