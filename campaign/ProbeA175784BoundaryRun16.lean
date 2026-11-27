import Mathlib

/-!
An independent boundary audit for the merged A175784 statement.

The OEIS recurrence is stated from `n = 11` because the source offset is one.
The statement's rational definition nevertheless has a natural value at `n = 0`.
With that extension the recurrence already holds at `n = 10`, while it fails at
the immediately preceding index `n = 9`.  These are direct evaluations of the
independent rational definition, not uses of the recurrence or of `main`.
-/

namespace A175784BoundaryRun16

def q (n : ℕ) : ℚ := (2 * (n : ℚ) - 1) / (2 * (n : ℚ) + 9) + 1

def a (n : ℕ) : ℤ := (q n).num

theorem exact_values :
    a 0 = 8 ∧ a 4 = 24 ∧ a 5 = 28 ∧ a 9 = 44 ∧ a 10 = 48 := by
  norm_num [a, q]

theorem recurrence_at_ten :
    a 10 = 2 * a (10 - 5) - a (10 - 10) := by
  norm_num [a, q]

theorem recurrence_fails_at_nine :
    a 9 ≠ 2 * a (9 - 5) - a (9 - 10) := by
  norm_num [a, q]

#print axioms exact_values
#print axioms recurrence_at_ten
#print axioms recurrence_fails_at_nine

end A175784BoundaryRun16
