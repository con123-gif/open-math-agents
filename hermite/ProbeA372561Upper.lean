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


/-
Existence and extremal bridges for the literal global minimum coin count.
These lemmas do not assume a greedy algorithm is optimal.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

open OMA.S_oeis_a372561

namespace A372561Certificate

@[simp] theorem value_zero : value (0 : Multiset ℕ) = 0 := by
  simp [value]

@[simp] theorem value_add (m t : Multiset ℕ) : value (m + t) = value m + value t := by
  simp [value]

@[simp] theorem value_single (i : ℕ) : value ({i} : Multiset ℕ) = jac i := by
  simp [value]

@[simp] theorem value_replicate (r i : ℕ) :
    value (Multiset.replicate r i) = r * jac i := by
  simp [value, nsmul_eq_mul]

theorem represents_ones (n : ℕ) : represents n (Multiset.replicate n 2) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have hi2 : i = 2 := (Multiset.mem_replicate.mp hi).2
    omega
  · simp [value, jac]

theorem minCoins_witness (n : ℕ) :
    ∃ m : Multiset ℕ, represents n m ∧ m.card = minCoins n := by
  have hs : {r : ℕ | ∃ m : Multiset ℕ, represents n m ∧ m.card = r}.Nonempty :=
    ⟨n, Multiset.replicate n 2, represents_ones n, by simp⟩
  unfold minCoins
  exact csInf_mem hs

theorem minCoins_le {n : ℕ} {m : Multiset ℕ} (hm : represents n m) :
    minCoins n ≤ m.card := by
  unfold minCoins
  exact csInf_le (OrderBot.bddBelow _) ⟨m, hm, rfl⟩

theorem minCoins_eq_of_bounds {n r : ℕ}
    (upper : ∃ m : Multiset ℕ, represents n m ∧ m.card = r)
    (lower : ∀ m : Multiset ℕ, represents n m → r ≤ m.card) : minCoins n = r := by
  obtain ⟨m, hm, hcard⟩ := upper
  apply le_antisymm
  · calc
      minCoins n ≤ m.card := minCoins_le hm
      _ = r := hcard
  · obtain ⟨t, ht, htcard⟩ := minCoins_witness n
    calc
      r ≤ t.card := lower t ht
      _ = minCoins n := htcard

theorem minCoins_pos {n : ℕ} (hn : 0 < n) : 0 < minCoins n := by
  apply Nat.pos_of_ne_zero
  intro hz
  obtain ⟨m, hm, hcard⟩ := minCoins_witness n
  have hm0 : m = 0 := Multiset.card_eq_zero.mp (hcard.trans hz)
  have hn0 : n = 0 := by simpa [hm0, value] using hm.2.symm
  omega

end A372561Certificate


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

#print axioms A372561Certificate.three_lift
#print axioms A372561Certificate.stretch_eq_lift
#print axioms A372561Certificate.valuation_lift
#print axioms A372561Certificate.reduced_lift
#print axioms A372561Certificate.stretch_lift

namespace A372561Certificate
open OMA.S_oeis_a372561

lemma alt_step (n : ℕ) :
    (n % 2 = 0 → jac (n + 1) = 2 * jac n + 1) ∧
    (n % 2 = 1 → 2 * jac n = jac (n + 1) + 1) := by
  induction n with
  | zero => norm_num [jac]
  | succ n ih =>
    have hr : jac (n + 2) = jac (n + 1) + 2 * jac n := rfl
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hh := ih.1 h
      constructor
      · intro hn
        omega
      · intro hn
        change 2 * jac (n + 1) = jac (n + 2) + 1
        rw [hr]
        omega
    · have hh := ih.2 h
      constructor
      · intro hn
        change jac (n + 2) = 2 * jac (n + 1) + 1
        rw [hr]
        omega
      · intro hn
        omega


lemma binary_formula (n : ℕ) :
    3 * jac n + (if n % 2 = 0 then 1 else 0) =
      2 ^ n + (if n % 2 = 1 then 1 else 0) := by
  induction n with
  | zero => norm_num [jac]
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have hn : (n + 1) % 2 = 1 := by omega
      have hs := (alt_step n).1 he
      simp only [he, hn, show ¬ (0 = 1) by decide, show ¬ (1 = 0) by decide,
        ↓reduceIte] at ih ⊢
      rw [pow_succ]
      omega
    · have hn : (n + 1) % 2 = 0 := by omega
      have hs := (alt_step n).2 ho
      simp only [ho, hn, show ¬ (0 = 1) by decide, show ¬ (1 = 0) by decide,
        ↓reduceIte] at ih ⊢
      rw [pow_succ]
      omega

def evenCount (m : Multiset ℕ) : ℕ :=
  (m.map fun i => if i % 2 = 0 then 1 else 0).sum

def oddCount (m : Multiset ℕ) : ℕ :=
  (m.map fun i => if i % 2 = 1 then 1 else 0).sum

def powerSum (m : Multiset ℕ) : ℕ := (m.map fun i => 2 ^ i).sum

lemma counts_card (m : Multiset ℕ) : evenCount m + oddCount m = m.card := by
  induction m using Multiset.induction_on with
  | empty => simp [evenCount, oddCount]
  | @cons i m ih =>
    rcases Nat.mod_two_eq_zero_or_one i with he | ho
    · simp [evenCount, oddCount, he] at *
      omega
    · simp [evenCount, oddCount, ho] at *
      omega

lemma jac_power_balance (m : Multiset ℕ) :
    3 * value m + evenCount m = powerSum m + oddCount m := by
  induction m using Multiset.induction_on with
  | empty => simp [value, evenCount, oddCount, powerSum]
  | @cons i m ih =>
    have hi := binary_formula i
    simp only [value, evenCount, oddCount, powerSum, Multiset.map_cons,
      Multiset.sum_cons] at ih ⊢
    omega

lemma D_power_two (i : ℕ) :
    D (2 ^ i) = if i % 2 = 0 then 1 else 2 := by
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · have hi : i = 2 * (i / 2) := by omega
    have hp : 2 ^ i = 4 ^ (i / 2) * 1 := by rw [hi, pow_mul]; norm_num
    rw [hp, D_shift]
    simp [he]
  · have hi : i = 2 * (i / 2) + 1 := by omega
    have hp : 2 ^ i = 4 ^ (i / 2) * 2 := by rw [hi, pow_add, pow_mul]; norm_num
    rw [hp, D_shift]
    simp [ho]

lemma D_double_power_two (i : ℕ) :
    D (2 * 2 ^ i) = if i % 2 = 0 then 2 else 1 := by
  have he : 2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ]; omega
  rw [he, D_power_two]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h, show (i + 1) % 2 = 1 - i % 2 by omega]

lemma power_weights (m : Multiset ℕ) :
    D (powerSum m) ≤ evenCount m + 2 * oddCount m ∧
    D (2 * powerSum m) ≤ 2 * evenCount m + oddCount m := by
  induction m using Multiset.induction_on with
  | empty => simp [powerSum, evenCount, oddCount]
  | @cons i m ih =>
    have ha := D_add_le (2 ^ i) (powerSum m)
    have hb := D_add_le (2 * 2 ^ i) (2 * powerSum m)
    have hpi := D_power_two i
    have hpdi := D_double_power_two i
    have hps : powerSum (i ::ₘ m) = 2 ^ i + powerSum m := by simp [powerSum]
    have hps2 : 2 * powerSum (i ::ₘ m) = 2 * 2 ^ i + 2 * powerSum m := by rw [hps]; omega
    rcases Nat.mod_two_eq_zero_or_one i with he | ho
    · simp only [he, if_true] at hpi hpdi
      have hcs : evenCount (i ::ₘ m) = 1 + evenCount m := by simp [evenCount, he]
      have hco : oddCount (i ::ₘ m) = oddCount m := by simp [oddCount, he]
      rw [hps, hps2, hcs, hco]
      omega
    · simp only [ho, show ¬ (1 = 0) by decide, if_false] at hpi hpdi
      have hcs : evenCount (i ::ₘ m) = evenCount m := by simp [evenCount, ho]
      have hco : oddCount (i ::ₘ m) = 1 + oddCount m := by simp [oddCount, ho]
      rw [hps, hps2, hcs, hco]
      omega

lemma powerSum_four_dvd {n : ℕ} {m : Multiset ℕ} (hm : represents n m) :
    4 ∣ powerSum m := by
  have hvalid := hm.1
  clear hm
  induction m using Multiset.induction_on with
  | empty => simp [powerSum]
  | @cons i m ih =>
    have hi : 2 ≤ i := hvalid i (by simp)
    have hrest : ∀ j ∈ m, 2 ≤ j := by intro j hj; exact hvalid j (by simp [hj])
    have hpow : 4 ∣ 2 ^ i := by
      refine ⟨2 ^ (i - 2), ?_⟩
      have he : i = 2 + (i - 2) := by omega
      rw [he, pow_add]
      norm_num
    simpa [powerSum] using dvd_add hpow (ih hrest)

end A372561Certificate

namespace A372561Certificate
open OMA.S_oeis_a372561

lemma shift_powerSum (m : Multiset ℕ) (E : ℕ) :
    powerSum (m.map (fun i => i + 2 * E)) = 4 ^ E * powerSum m := by
  induction m using Multiset.induction_on with
  | empty => simp [powerSum]
  | @cons i m ih =>
    have hp : 2 ^ (i + 2 * E) = 4 ^ E * 2 ^ i := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    simp only [Multiset.map_cons, powerSum, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [hp, ih]
    ring

lemma shift_evenCount (m : Multiset ℕ) (E : ℕ) :
    evenCount (m.map (fun i => i + 2 * E)) = evenCount m := by
  simp [evenCount, Multiset.map_map, Function.comp_def, Nat.add_mod]

lemma shift_oddCount (m : Multiset ℕ) (E : ℕ) :
    oddCount (m.map (fun i => i + 2 * E)) = oddCount m := by
  simp [oddCount, Multiset.map_map, Function.comp_def, Nat.add_mod]

lemma lift_upper_witness {y R E : ℕ} (hE : 1 ≤ E) (w : List ℕ)
    (hp : powerSum (w : Multiset ℕ) = 3 * y + 1)
    (hc : evenCount (w : Multiset ℕ) = oddCount (w : Multiset ℕ) + 1)
    (hr : w.length = R) :
    ∃ m : Multiset ℕ, represents (lift E y) m ∧ m.card = R := by
  let m : Multiset ℕ := (w : Multiset ℕ).map (fun i => i + 2 * E)
  have hvalid : ∀ i ∈ m, 2 ≤ i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
    omega
  have hbalance := jac_power_balance m
  have he : evenCount m = evenCount (w : Multiset ℕ) := shift_evenCount _ _
  have ho : oddCount m = oddCount (w : Multiset ℕ) := shift_oddCount _ _
  have hpow : powerSum m = 4 ^ E * (3 * y + 1) := by
    change powerSum ((w : Multiset ℕ).map (fun i => i + 2 * E)) = _
    rw [shift_powerSum, hp]
  have hl := three_lift E y
  refine ⟨m, ⟨hvalid, ?_⟩, ?_⟩
  · nlinarith
  · simpa [m] using hr


end A372561Certificate

#print axioms A372561Certificate.lift_upper_witness
