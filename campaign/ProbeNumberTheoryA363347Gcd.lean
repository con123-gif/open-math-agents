import Mathlib

/-!
Counterexample to the gcd-pairing formula in OEIS A363347 revision 43.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6.2).
Source: Mohammed Bouras, https://oeis.org/A363347.
This does not dispute the previously established prime occurrence claims.
The literal continued fraction is used, not the disputed gcd formula.
-/
namespace A363347Gcd
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def tail (n : ℕ) : ℕ → ℚ
  | 0 => -4
  | j+1 => ((n - (j+1) : ℕ) : ℚ) -
      ((n-j : ℕ) : ℚ) / tail n j

def a (n : ℕ) : ℕ := (1 / tail n (n-2)).den
def poly (n : ℕ) : ℕ := n^2 + 2*n - 4

theorem small116 : a 116 = 311 := by decide
theorem small193 : a 193 = 311 := by decide
theorem gcd_value : Nat.gcd (poly 116) (poly 193) = 3421 := by decide

theorem disproof : ¬ (∀ n m : ℕ, 3 ≤ n → 3 ≤ m → n ≠ m →
    a n = a m → a n ≠ 1 → a n = Nat.gcd (poly n) (poly m)) := by
  intro h
  have hc := h 116 193 (by decide) (by decide) (by decide)
    (small116.trans small193.symm) (by rw [small116]; decide)
  rw [small116, gcd_value] at hc
  norm_num at hc

end A363347Gcd
#print axioms A363347Gcd.disproof
