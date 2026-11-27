import Mathlib

/-
Bernoulli denominator bridge for A068991.
First stage: actual pinned API availability, before using the theorem in
the full bridge. No source conjecture is assumed.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
-/

open Finset
open scoped BigOperators

namespace A068991Certificate

theorem bernoulli_integral_available (k : ℕ) :
    bernoulli (2 * k) +
      ∑ p ∈ range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
        (1 : ℚ) / p ∈ Set.range (Int.cast : ℤ → ℚ) :=
  Bernoulli.vonStaudt_clausen k

end A068991Certificate

#check Bernoulli.vonStaudt_clausen
#print axioms Bernoulli.vonStaudt_clausen
#print axioms A068991Certificate.bernoulli_integral_available
