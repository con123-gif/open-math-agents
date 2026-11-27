import Mathlib

/-
Source: taobaozhe, MathOverflow question 511647, May 25, 2026.
https://mathoverflow.net/questions/511647
Question text licensed CC BY-SA 4.0.
Adaptation: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).

The rows and columns below are labelled by pairs 0 <= i <= j < n,
ordered first by j and then by i. This is the monomial ordering
(0,0),(0,1),(1,1); (0,2),(1,2),(2,2); ... . Its cardinality is
n(n+1)/2, and the consecutive column blocks have lengths 3,3,4,...,n.
The three branches of `matrix` are respectively U_n, the first n-1
rows of L_n, and the final row of L_n. Natural subtraction i-1 sends
both 0 and 1 to 0, exactly the two initial 1s in each C_j.

The source's displayed block construction applies for odd n >= 3.
Both boxed assertions are retained: the exact characteristic polynomial
with its multiplicities, and the proposed stronger matrix-power identity.
No numerical experiments or symmetric-square property are hypotheses.
-/

namespace OMA.S_mo_511647

abbrev Pair (n : ℕ) := { p : Fin n × Fin n // p.1 ≤ p.2 }

def matrix (n : ℕ) : Matrix (Pair n) (Pair n) ℤ := fun row col =>
  if row.val.2.val + 1 < n then
    if row.val.1.val = col.val.1.val - 1 ∧
       row.val.2.val = col.val.2.val - 1 then 1 else 0
  else if row.val.1.val + 1 < n then
    -(if col.val.2.val ≠ 0 ∧ row.val.1.val = col.val.1.val - 1 then 1 else 0) -
      (if col.val.1.val ≠ 0 ∧ row.val.1.val = col.val.2.val - 1 then 1 else 0)
  else
    if col.val.1.val = 0 then 0 else 1

theorem main :
  ∀ n : ℕ, 3 ≤ n → Odd n →
    (matrix n).charpoly = (Polynomial.X ^ n - 1) ^ ((n + 1) / 2) ∧
    matrix n ^ n = 1 := by
  sorry

end OMA.S_mo_511647
