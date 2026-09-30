def normalize(text)
  text.gsub(/0x[0-9a-f]+/, "0xADDR")
end
def inspect_root(label)
  p [label, normalize($root.inspect), $hook_calls, $leaf_calls]
rescue StandardError => e
  p [label, e.class, e.message]
end
class GuardRoot
  private
  def instance_variables_to_inspect
    $hook_calls += 1
    nil
  end
end
class GuardLeaf
  def inspect
    $leaf_calls += 1
    raise "inspection escaped" if $mode == :raise
    throw :guard, :escaped if $mode == :throw
    return $renderer if $mode == :coerce
    if $pause
      $pause = false
      $yielder << :inspection_paused
    end
    $root.inspect
  end
end
class GuardRenderer
  def to_s
    $root.inspect
  end
end
$hook_calls = 0
$leaf_calls = 0
$mode = :normal
$pause = false
$renderer = GuardRenderer.new
$root = GuardRoot.new
$root.instance_variable_set(:@leaf, GuardLeaf.new)
inspect_root(:recursive)
inspect_root(:recursive_again)
$mode = :raise
inspect_root(:raise_cleanup)
$mode = :normal
inspect_root(:after_raise)
$mode = :throw
p [:throw_cleanup, catch(:guard) { $root.inspect }]
$mode = :normal
inspect_root(:after_throw)
$mode = :coerce
inspect_root(:stringification_guard)
$mode = :normal
enum = Enumerator.new do |y|
  $yielder = y
  $pause = true
  y << $root.inspect
  :producer_done
end
p [:suspend, enum.next]
inspect_root(:caller_independent_guard)
p [:resume, normalize(enum.next)]
begin
  enum.next
rescue StopIteration => e
  p [:finished, e.result]
end
inspect_root(:after_completion)
p [:suspend_again, enum.rewind.next]
enum.rewind
inspect_root(:after_abandonment)
nil
