/-!
Base4 digit-weight lift identities for A372561.
Prerequisite: the unchanged a372561_digits_helpers.lean in the same namespace.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidates await pinned checking.
-/

namespace A372561Certificate

lemma D_shift_right (n e : ℕ) : D (n * 4 ^ e) = D n := by
  simpa [Nat.mul_comm] using D_shift n e

lemma D_plus_four {q E : ℕ} (hq : q % 2 = 0) (hE : 1 ≤ E) :
    D (q * 4 ^ E + 4) = D q + 1 ∧
      D (2 * (q * 4 ^ E + 4)) = D (2 * q) + 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  let a := q / 2
  have hqa : q = 2 * a := by dsimp [a]; omega
  have hpow : q * 4 ^ (e + 1) = 4 * (q * 4 ^ e) := by
    rw [pow_succ]
    ring
  have hA : q * 4 ^ e = 2 * (a * 4 ^ e) := by rw [hqa]; ring
  have he1 : q * 4 ^ (e + 1) + 4 = 4 * (2 * (a * 4 ^ e) + 1) := by
    rw [hpow, hA]
    ring
  have he2 : 2 * (q * 4 ^ (e + 1) + 4) = 4 * (4 * (a * 4 ^ e) + 2) := by
    rw [he1]
    ring
  have hdA : D (2 * (a * 4 ^ e)) = D q := by
    rw [← hA]
    exact D_shift_right q e
  have hd2A : D (a * 4 ^ e) = D (2 * q) := by
    have ht : (2 * q) * 4 ^ e = 4 * (a * 4 ^ e) := by rw [hqa]; ring
    have hs := D_shift_right (2 * q) e
    rw [ht, D_mul_four] at hs
    exact hs
  constructor
  · rw [he1, D_mul_four, D_even_succ, hdA]
  · rw [he2, D_mul_four, D_step _ 2 (by decide), hd2A]

lemma D_minus_four {q E : ℕ} (hq : 1 ≤ q) (hE : 1 ≤ E) :
    D (q * 4 ^ E - 4) = D (q - 1) + 3 * (E - 1) ∧
      D (2 * (q * 4 ^ E - 4)) = D (2 * (q - 1)) + 3 * (E - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hp : 0 < 4 ^ e := by positivity
  have hprod : 1 ≤ q * 4 ^ e := by
    have hpos := Nat.mul_pos (by omega : 0 < q) hp
    omega
  have hpow : q * 4 ^ (e + 1) = 4 * (q * 4 ^ e) := by
    rw [pow_succ]
    ring
  have he1 : q * 4 ^ (e + 1) - 4 = 4 * (q * 4 ^ e - 1) := by
    rw [hpow]
    omega
  have he2 : 2 * (q * 4 ^ (e + 1) - 4) = 4 * (2 * (q * 4 ^ e - 1)) := by
    rw [he1]
    ring
  constructor
  · rw [he1, D_mul_four, D_borrow q e hq]
  · rw [he2, D_mul_four, D_double_borrow q e hq]

lemma D_double_minus_eight {q E : ℕ} (hq : 1 ≤ q) (hE : 2 ≤ E) :
    D (2 * (q * 4 ^ E - 8)) = D (2 * (q - 1)) + 1 + 3 * (E - 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 2 := ⟨E - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hp : 0 < 4 ^ e := by positivity
  have hprod : 1 ≤ q * 4 ^ e := by
    have hpos := Nat.mul_pos (by omega : 0 < q) hp
    omega
  have hpow : q * 4 ^ (e + 2) = 16 * (q * 4 ^ e) := by
    rw [pow_add]
    norm_num
    ring
  have htwo : (2 * q) * 4 ^ e = 2 * (q * 4 ^ e) := by ring
  have he : 2 * (q * 4 ^ (e + 2) - 8) = 16 * ((2 * q) * 4 ^ e - 1) := by
    rw [hpow, htwo]
    omega
  have hs : D (16 * ((2 * q) * 4 ^ e - 1)) = D ((2 * q) * 4 ^ e - 1) := by
    simpa using D_shift ((2 * q) * 4 ^ e - 1) 2
  have hpred : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
  rw [he, hs, D_borrow (2 * q) e (by omega), hpred, D_even_succ]

end A372561Certificate
