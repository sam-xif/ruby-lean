import Checker.Audit.Derive

namespace Checker.Audit

def rulesEnabled (enabled : String → Bool) (used : List String) : Bool := used.all enabled

theorem trace_head {enabled : String → Bool} {rule : String} {tail : List String}
    (h : rulesEnabled enabled (rule :: tail) = true) : enabled rule = true :=
  (Bool.and_eq_true_iff.mp h).1

theorem trace_tail {enabled : String → Bool} {rule : String} {tail : List String}
    (h : rulesEnabled enabled (rule :: tail) = true) : rulesEnabled enabled tail = true :=
  (Bool.and_eq_true_iff.mp h).2

theorem trace_left {enabled : String → Bool} {xs ys : List String}
    (h : rulesEnabled enabled (xs ++ ys) = true) : rulesEnabled enabled xs = true := by
  unfold rulesEnabled at *
  rw [List.all_append] at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem trace_right {enabled : String → Bool} {xs ys : List String}
    (h : rulesEnabled enabled (xs ++ ys) = true) : rulesEnabled enabled ys = true := by
  unfold rulesEnabled at *
  rw [List.all_append] at h
  exact (Bool.and_eq_true_iff.mp h).2
end Checker.Audit
