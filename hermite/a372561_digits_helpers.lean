import Mathlib

/-!
Base4 digit-weight infrastructure for the complete A372561 lift argument.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Complete candidates await pinned checking.
-/

namespace A372561Certificate

def D (n : ℕ) : ℕ := (Nat.digits 4 n).sum

@[simp] lemma D_zero : D 0 = 0 := by simp [D]
@[simp] lemma D_one : D 1 = 1 := by norm_num [D, Nat.digits_of_lt]
@[simp] lemma D_two : D 2 = 2 := by norm_num [D, Nat.digits_of_lt]

lemma D_step (q r : ℕ) (hr : r < 4) : D (4 * q + r) = D q + r := by
  by_cases hz : q = 0 ∧ r = 0
  · rcases hz with ⟨rfl, rfl⟩
    simp
  · have hh : r ≠ 0 ∨ q ≠ 0 := by omega
    have hd := Nat.digits_add 4 (by decide) r q hr hh
    have he : 4 * q + r = r + 4 * q := by omega
    rw [D, he, hd]
    simp [D, Nat.add_comm]

lemma D_quotient (n : ℕ) : D n = D (n / 4) + n % 4 := by
  have h := D_step (n / 4) (n % 4) (Nat.mod_lt _ (by decide))
  have he : 4 * (n / 4) + n % 4 = n := by omega
  rw [he] at h
  exact h

@[simp] lemma D_mul_four (n : ℕ) : D (4 * n) = D n := by
  simpa using D_step n 0 (by decide)

lemma D_shift (n e : ℕ) : D (4 ^ e * n) = D n := by
  induction e with
  | zero => simp
  | succ e ih =>
    have he : 4 ^ (e + 1) * n = 4 * (4 ^ e * n) := by rw [pow_succ]; ring
    rw [he, D_mul_four, ih]

lemma D_succ_le (n : ℕ) : D (n + 1) ≤ D n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp
    · have hq : n / 4 < n := Nat.div_lt_self (by omega) (by decide)
      have hd := D_quotient n
      have hr := Nat.mod_lt n (by decide : 0 < 4)
      by_cases hc : n % 4 < 3
      · have he : n + 1 = 4 * (n / 4) + (n % 4 + 1) := by omega
        rw [he, D_step _ _ (by omega)]
        omega
      · have h3 : n % 4 = 3 := by omega
        have he : n + 1 = 4 * (n / 4 + 1) := by omega
        rw [he, D_mul_four]
        have hh := ih (n / 4) hq
        omega

lemma D_add_le (a b : ℕ) : D (a + b) ≤ D a + D b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a
      simp
    · have hq : a / 4 < a := Nat.div_lt_self (by omega) (by decide)
      have hh := ih (a / 4) hq (b / 4)
      have hda := D_quotient a
      have hdb := D_quotient b
      have hra := Nat.mod_lt a (by decide : 0 < 4)
      have hrb := Nat.mod_lt b (by decide : 0 < 4)
      by_cases hc : a % 4 + b % 4 < 4
      · have he : a + b = 4 * (a / 4 + b / 4) + (a % 4 + b % 4) := by omega
        rw [he, D_step _ _ hc]
        omega
      · have he : a + b = 4 * (a / 4 + b / 4 + 1) + (a % 4 + b % 4 - 4) := by omega
        rw [he, D_step _ _ (by omega)]
        have hs := D_succ_le (a / 4 + b / 4)
        omega

lemma D_even_succ (a : ℕ) : D (2 * a + 1) = D (2 * a) + 1 := by
  have ha : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have hd : a % 2 + 2 * (a / 2) = a := by omega
  have he0 : 2 * a = 4 * (a / 2) + 2 * (a % 2) := by omega
  have he1 : 2 * a + 1 = 4 * (a / 2) + (2 * (a % 2) + 1) := by omega
  rw [he1, he0, D_step _ _ (by omega), D_step _ _ (by omega)]
  omega

lemma D_borrow (a e : ℕ) (ha : 1 ≤ a) :
    D (a * 4 ^ e - 1) = D (a - 1) + 3 * e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hp : 0 < 4 ^ e := by positivity
    have hprod : 1 ≤ a * 4 ^ e := by
      have hpos := Nat.mul_pos (by omega : 0 < a) hp
      omega
    have hpow : a * 4 ^ (e + 1) = 4 * (a * 4 ^ e) := by
      rw [pow_succ]
      ring
    have he : a * 4 ^ (e + 1) - 1 = 4 * (a * 4 ^ e - 1) + 3 := by
      rw [hpow]
      omega
    rw [he, D_step _ _ (by decide), ih]
    omega

lemma D_double_borrow (a e : ℕ) (ha : 1 ≤ a) :
    D (2 * (a * 4 ^ e - 1)) = D (2 * (a - 1)) + 3 * e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hp : 0 < 4 ^ e := by positivity
    have hprod : 1 ≤ a * 4 ^ e := by
      have hpos := Nat.mul_pos (by omega : 0 < a) hp
      omega
    have hpow : a * 4 ^ (e + 1) = 4 * (a * 4 ^ e) := by
      rw [pow_succ]
      ring
    have he : 2 * (a * 4 ^ (e + 1) - 1) = 4 * (2 * (a * 4 ^ e - 1) + 1) + 2 := by
      rw [hpow]
      omega
    rw [he, D_step _ _ (by decide), D_even_succ, ih]
    omega

lemma D_double_pred {q : ℕ} (hq : 2 ≤ q) (he : q % 2 = 0) :
    D (2 * (q - 1)) ≥ D (2 * q) + 1 := by
  have hq2 : 1 ≤ q / 2 := by omega
  have he1 : 2 * (q - 1) = 4 * (q / 2 - 1) + 2 := by omega
  have he2 : 2 * q = 4 * (q / 2) := by omega
  rw [he1, D_step _ _ (by decide), he2, D_mul_four]
  have hs := D_succ_le (q / 2 - 1)
  have hx : q / 2 - 1 + 1 = q / 2 := by omega
  rw [hx] at hs
  omega

lemma D_le_double (q : ℕ) : D q ≤ 2 * D (2 * q) := by
  have hh := D_add_le (2 * q) (2 * q)
  have he : 2 * q + 2 * q = 4 * q := by omega
  rw [he, D_mul_four] at hh
  omega

end A372561Certificate
