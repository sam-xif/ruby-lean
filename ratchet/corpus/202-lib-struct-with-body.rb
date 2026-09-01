Status = Struct.new(:state, keyword_init: true) do
  def affected?
    state == :affected
  end
end

Status.new(state: :affected).affected?
