import Mathlib

/-
Generic iteration reduction for A372561. Assemble after the faithful source
statement and a372561_valuation_helpers.lean. No orbit table, minimum-count
claim, or valuation identity is assumed here.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Candidate awaiting pinned verification; no full-solution claim.
-/

namespace A372561Certificate

open OMA.S_oeis_a372561

theorem stretch_iterate_lift (m y : ℕ) :
    ∃ E : ℕ,
      (stretch^[m + 1]) y = lift E ((reduced^[m + 1]) y) ∧
      valuation ((reduced^[m]) y) ≤ E := by
  induction m with
  | zero =>
    refine ⟨valuation y, ?_, ?_⟩
    · simpa using stretch_eq_lift y
    · simp
  | succ m ih =>
    obtain ⟨E, hE, hbound⟩ := ih
    refine ⟨2 * E + valuation ((reduced^[m + 1]) y), ?_, ?_⟩
    · rw [Function.iterate_succ_apply' stretch (m + 1) y, hE, stretch_lift,
        Function.iterate_succ_apply' reduced (m + 1) y]
    · simpa only [Nat.succ_eq_add_one] using
        (show valuation ((reduced^[m + 1]) y) ≤
          2 * E + valuation ((reduced^[m + 1]) y) by omega)

theorem grid_lift (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∃ E : ℕ,
      grid n k = lift E ((reduced^[n + k - 2]) 27) ∧
      valuation ((reduced^[n + k - 3]) 27) ≤ E := by
  obtain ⟨E, hE, hbound⟩ :=
    stretch_iterate_lift (n - 2) ((reduced^[k - 1]) 27)
  have hn1 : n - 2 + 1 = n - 1 := by omega
  have hsum1 : n - 2 + 1 + (k - 1) = n + k - 2 := by omega
  have hsum0 : n - 2 + (k - 1) = n + k - 3 := by omega
  refine ⟨E, ?_, ?_⟩
  · calc
      grid n k = (stretch^[n - 2 + 1]) ((reduced^[k - 1]) 27) := by
        simp only [grid, hn1]
      _ = lift E ((reduced^[n - 2 + 1]) ((reduced^[k - 1]) 27)) := hE
      _ = lift E ((reduced^[n + k - 2]) 27) := by
        rw [← Function.iterate_add_apply, hsum1]
  · simpa only [← Function.iterate_add_apply, hsum0] using hbound

end A372561Certificate

#print axioms A372561Certificate.stretch_iterate_lift
#print axioms A372561Certificate.grid_lift
