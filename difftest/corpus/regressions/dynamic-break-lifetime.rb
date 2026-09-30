def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end

def capture(&block)
  block
end

def relay(&block)
  block.call
  :unreachable
ensure
  puts :relay_ensure
end

def original(&block)
  relay(&block)
  :unreachable
ensure
  puts :original_ensure
end

show(:forwarded_break) { original { break 11 } }
dead = capture { break 12 }
show(:dead_break) { dead.call }
show(:dead_break_again) { dead.call }
normal = capture { :ordinary_value }
show(:dead_normal_call) { normal.call }

$saved = nil
def call_in_ensure(&block)
  $saved = block
  :body_value
ensure
  block.call
end
show(:live_during_ensure) { call_in_ensure { break 13 } }
show(:expired_after_ensure) { $saved.call }

class BreakConstructor
  def initialize(&block)
    block.call
  ensure
    puts :initialize_ensure
  end
end
show(:constructor_break) { BreakConstructor.new { break 14 } }

def recursive(depth, &block)
  return block.call if depth == 0
  recursive(depth - 1) { break block.call }
ensure
  p [:recursive_ensure, depth]
end
show(:recursive_tokens) { recursive(2) { break 15 } }

def across_execution(&block)
  Enumerator.new { |y| block.call; y << :unreachable }.next
end
show(:other_execution) { across_execution { break 16 } }

enum = Enumerator.new do |y|
  [1, 2].each do |n|
    y << n
    break :producer_done
  end
end
show(:suspended_producer) { enum.next }
begin
  enum.next
rescue StopIteration => e
  p [:resumed_break, e.result]
end

$resume_saved = false
enum = Enumerator.new do |y|
  call_in_ensure do
    break :producer_done if $resume_saved
    y << :suspended
    break :producer_done
  end
end
show(:rewind_suspend) { enum.next }
enum.rewind
$resume_saved = true
show(:abandoned_token) { $saved.call }
$resume_saved = false
show(:rewind_fresh_token) { enum.next }
$resume_saved = true
show(:fresh_token_other_execution) { $saved.call }
