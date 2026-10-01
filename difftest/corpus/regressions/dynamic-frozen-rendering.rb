def normalize(text)
  text.gsub(/0x[0-9a-f]+/, "0xADDR")
end
def mutation(label)
  $trace = []
  $receiver.instance_variable_set(:@x, 1)
rescue StandardError => e
  p [label, e.class, normalize(e.message), $trace]
end
class FrozenError
  def initialize(message)
    $trace << :initialize
    if $during_initialize
      $during_initialize = false
      $receiver.instance_variable_set(:@x, 1)
    end
    super(message)
  end
end
class FrozenRenderer
  def to_s
    $trace << :stringify
    $receiver.instance_variable_set(:@x, 1)
  end
end
class FrozenGuard
  def self.to_s
    $trace << :class_name
    if $during_class_name
      $during_class_name = false
      $receiver.instance_variable_set(:@x, 1)
    end
    "FrozenGuard"
  end
  def inspect
    $trace << :inspect
    if $mode == :recursive
      $receiver.instance_variable_set(:@x, 1)
    elsif $mode == :stringify
      $renderer
    elsif $mode == :other_receiver
      $other.instance_variable_set(:@x, 1)
    elsif $mode == :raise
      raise "rendering escaped"
    elsif $mode == :throw
      throw :rendering, :escaped
    else
      if $pause
        $pause = false
        $yielder << :rendering_paused
      end
      "RENDERED"
    end
  end
end
$during_initialize = false
$during_class_name = false
$pause = false
$renderer = FrozenRenderer.new
$receiver = FrozenGuard.new.freeze
$other = Object.new.freeze
$mode = :recursive
mutation(:recursive)
mutation(:recursive_again)
$mode = :stringify
mutation(:stringification)
$mode = :other_receiver
mutation(:different_identity)
$mode = :raise
mutation(:raise_cleanup)
$mode = :throw
$trace = []
p [:throw_cleanup, catch(:rendering) { $receiver.instance_variable_set(:@x, 1) }, $trace]
$mode = :normal
mutation(:after_escape)
$during_initialize = true
mutation(:initializer_before_guard)
$during_class_name = true
mutation(:class_name_before_guard)
enum = Enumerator.new do |y|
  $yielder = y
  $pause = true
  begin
    $receiver.instance_variable_set(:@x, 1)
  rescue FrozenError => e
    y << e.message
  end
  :producer_done
end
$trace = []
p [:suspended, enum.next, $trace]
mutation(:caller_independent_guard)
p [:resumed, normalize(enum.next)]
begin
  enum.next
rescue StopIteration => e
  p [:finished, e.result]
end
mutation(:after_completion)
p [:suspended_again, enum.rewind.next]
enum.rewind
mutation(:after_abandonment)
nil
