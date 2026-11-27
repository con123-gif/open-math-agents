import Mathlib

/-!
OEIS A372561, conjectures by Antti Karttunen, May 2024.
Sources: A372561 (comments), A372560, A371094, A372443 and A372555.
A372561's displayed table uses the GREEDY count A265745. The selected
three conjectures explicitly use the GLOBAL MINIMUM count A372555,
represented by `minCoins` below, on the raw array A372560 (`grid`).
The thirteenth upward antidiagonal has n+k=14 and begins233,933,...;
the thirtieth has n+k=31 and begins911,58325,... . The first two
claims omit the first entry of their respective antidiagonal. The third
is symmetry of the minimum-count array away from the first row/column.
Jacobsthal index1 duplicates index2; zero coins and duplicate index1
can be omitted from globally minimum-cardinality representations.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/
namespace OMA.S_oeis_a372561

def jac : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jac (n + 1) + 2 * jac n

def value (m : Multiset ℕ) : ℕ := (m.map jac).sum

def represents (n : ℕ) (m : Multiset ℕ) : Prop :=
  (∀ i ∈ m, 2 ≤ i) ∧ value m = n

noncomputable def minCoins (n : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ m : Multiset ℕ, represents n m ∧ m.card = r}

def valuation (n : ℕ) : ℕ := padicValNat 2 (3 * n + 1)

def reduced (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ valuation n

def lift (e y : ℕ) : ℕ := 4 ^ e * y + (4 ^ e - 1) / 3

def stretch (n : ℕ) : ℕ :=
  (3 * n + 1) * 2 ^ valuation n + (4 ^ valuation n - 1) / 3

def grid (n k : ℕ) : ℕ :=
  (stretch^[n - 1]) ((reduced^[k - 1]) 27)

end OMA.S_oeis_a372561


/-
Exact arithmetic helpers for the source-defined A372561 transformations.
Assemble after the faithful statement. No conjecture or valuation identity
is assumed; all valuations are the genuine padicValNat 2.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Helper candidate awaiting the pinned checker; no full-solution claim.
-/

namespace A372561Certificate

open OMA.S_oeis_a372561

theorem four_pow_two (E : ℕ) : 4 ^ E = 2 ^ (2 * E) := by
  calc
    4 ^ E = (2 ^ 2) ^ E := rfl
    _ = 2 ^ (2 * E) := (pow_mul 2 2 E).symm

theorem four_pow_square (E : ℕ) : 4 ^ E = (2 ^ E) ^ 2 := by
  calc
    4 ^ E = 2 ^ (2 * E) := four_pow_two E
    _ = 2 ^ (E * 2) := by rw [Nat.mul_comm 2 E]
    _ = (2 ^ E) ^ 2 := pow_mul 2 E 2

theorem three_dvd_four_pow_sub_one (E : ℕ) : 3 ∣ 4 ^ E - 1 := by
  have hp : 0 < 4 ^ E := pow_pos (by decide) E
  have hm : 4 ^ E % 3 = 1 := by norm_num [Nat.pow_mod]
  apply Nat.dvd_of_mod_eq_zero
  omega

theorem three_lift (E y : ℕ) :
    3 * lift E y + 1 = (3 * y + 1) * 4 ^ E := by
  have hq : 3 * ((4 ^ E - 1) / 3) = 4 ^ E - 1 :=
    Nat.mul_div_cancel' (three_dvd_four_pow_sub_one E)
  have hp : 0 < 4 ^ E := pow_pos (by decide) E
  have hs : 4 ^ E - 1 + 1 = 4 ^ E := Nat.sub_add_cancel (by omega)
  unfold lift
  nlinarith

@[simp] theorem lift_zero (y : ℕ) : lift 0 y = y := by
  simp [lift]

@[simp] theorem lift_one (y : ℕ) : lift 1 y = 4 * y + 1 := by
  norm_num [lift]

theorem valuation_dvd (y : ℕ) : 2 ^ valuation y ∣ 3 * y + 1 :=
  pow_padicValNat_dvd

theorem reduced_mul_pow (y : ℕ) :
    2 ^ valuation y * reduced y = 3 * y + 1 := by
  exact Nat.mul_div_cancel' (valuation_dvd y)

theorem stretch_eq_lift (y : ℕ) : stretch y = lift (valuation y) (reduced y) := by
  unfold stretch lift
  congr 1
  rw [← reduced_mul_pow y, four_pow_square]
  ring

theorem valuation_lift (E y : ℕ) :
    valuation (lift E y) = 2 * E + valuation y := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold valuation
  rw [three_lift]
  rw [padicValNat.mul (by omega : 3 * y + 1 ≠ 0)
    (by positivity : 4 ^ E ≠ 0)]
  rw [four_pow_two, padicValNat.prime_pow]
  omega

theorem reduced_lift (E y : ℕ) : reduced (lift E y) = reduced y := by
  unfold reduced
  rw [three_lift, valuation_lift, pow_add, ← four_pow_two]
  rw [Nat.mul_comm (3 * y + 1) (4 ^ E)]
  exact Nat.mul_div_mul_left (3 * y + 1) (2 ^ valuation y) (by positivity : 0 < 4 ^ E)

theorem stretch_lift (E y : ℕ) :
    stretch (lift E y) = lift (2 * E + valuation y) (reduced y) := by
  rw [stretch_eq_lift, valuation_lift, reduced_lift]

end A372561Certificate



/-
Exact factorization certificates for the A372561 reduced Collatz orbit.
Assemble after the faithful statement; no valuation computation or orbit
identity is assumed. All finite inputs reduce to integer equalities and
oddness tests.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Candidate awaiting pinned verification.
-/

namespace A372561Certificate

open OMA.S_oeis_a372561

theorem valuation_of_factor (y v z : ℕ)
    (hf : 3 * y + 1 = 2 ^ v * z) (hz : 0 < z) (ho : z % 2 = 1) :
    valuation y = v := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ z := by
    intro hd
    have hm : z % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  unfold valuation
  rw [hf, padicValNat.mul (by positivity : 2 ^ v ≠ 0) (by omega : z ≠ 0),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnd, Nat.add_zero]

theorem reduced_of_factor (y v z : ℕ)
    (hf : 3 * y + 1 = 2 ^ v * z) (hz : 0 < z) (ho : z % 2 = 1) :
    reduced y = z := by
  unfold reduced
  rw [valuation_of_factor y v z hf hz ho, hf]
  exact Nat.mul_div_cancel_left z (by positivity : 0 < 2 ^ v)

theorem factor_data (y v z : ℕ)
    (hf : 3 * y + 1 = 2 ^ v * z) (hz : 0 < z) (ho : z % 2 = 1) :
    valuation y = v ∧ reduced y = z :=
  ⟨valuation_of_factor y v z hf hz ho, reduced_of_factor y v z hf hz ho⟩

end A372561Certificate



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


#print axioms A372561Certificate.factor_data
#print axioms A372561Certificate.grid_lift
