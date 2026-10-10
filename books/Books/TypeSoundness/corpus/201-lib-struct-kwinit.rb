# typed: true
Status = Struct.new(:state, :fixed_in, keyword_init: true)
s = Status.new(state: :affected, fixed_in: "1.0")
s.state == :affected
