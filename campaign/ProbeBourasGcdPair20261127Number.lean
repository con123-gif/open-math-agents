import Mathlib

/- Research-only probe: two supplementary gcd-pairing identities.
   Sources: Mohammed Bouras, OEIS A356247 and A363347, and arXiv:2509.09745v1 sec. 2.
   Credit Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 family).
   No novelty or official eligibility claim. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BourasGcdPairAudit

-- At step t+1, prepend (n-t-1) - (n-t)/previous.
def inner (x : ℚ) (n : ℕ) : ℕ → ℚ
  | 0 => x
  | t+1 => (↑(n-t-1) : ℚ) - (↑(n-t) : ℚ) / inner x n t

def a (k n : ℕ) : ℕ :=
  (1 / inner (-(k : ℚ)) n (n-2)).den

def Q (k n : ℕ) : ℕ := n*n + k*n - 2*n - k

-- Paper's positive-index prime-pair identity (A356247).
def claim356247 : Prop :=
  ∀ n m : ℕ, 3 ≤ n → 3 ≤ m → n ≠ m →
    Nat.Prime (a 1 n) → a 1 n = a 1 m →
    a 1 n = Nat.gcd (Q 1 n) (Q 1 m)

-- OEIS A363347: distinct indices, equal values different from 1.
def claim363347 : Prop :=
  ∀ n m : ℕ, 3 ≤ n → 3 ≤ m → n ≠ m →
    a 4 n ≠ 1 → a 4 n = a 4 m →
    a 4 n = Nat.gcd (Q 4 n) (Q 4 m)

theorem values356247 : a 1 62 = 199 ∧ a 1 138 = 199 ∧
    Nat.gcd (Q 1 62) (Q 1 138) = 3781 := by
  decide

theorem values363347 : a 4 116 = 311 ∧ a 4 193 = 311 ∧
    Nat.gcd (Q 4 116) (Q 4 193) = 3421 := by
  decide

theorem disproof356247 : ¬ claim356247 := by
  intro h
  obtain ⟨hn, hm, hg⟩ := values356247
  have hp : Nat.Prime (a 1 62) := by rw [hn]; norm_num
  have he : a 1 62 = a 1 138 := hn.trans hm.symm
  have hc := h 62 138 (by decide) (by decide) (by decide) hp he
  rw [hn, hg] at hc
  norm_num at hc

theorem disproof363347 : ¬ claim363347 := by
  intro h
  obtain ⟨hn, hm, hg⟩ := values363347
  have hp : a 4 116 ≠ 1 := by rw [hn]; decide
  have he : a 4 116 = a 4 193 := hn.trans hm.symm
  have hc := h 116 193 (by decide) (by decide) (by decide) hp he
  rw [hn, hg] at hc
  norm_num at hc

#print axioms disproof356247
#print axioms disproof363347
end BourasGcdPairAudit
