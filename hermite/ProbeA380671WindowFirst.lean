import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-!
Exact arithmetic window for the A380671 displacement-bound disproof.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
Model: GPT-6 (exact serving variant not exposed by this runtime).

This fragment has not yet been kernel-checked. It uses actual Nat.digits,
rather than leading-zero padding. The greedy sequence and parity argument
are supplied in separate fragments.
-/

namespace A380671Certificate

def Q : ℕ := Nat.factorial 100

def center : ℕ := Q * (10 ^ 200 + 1)

theorem center_gt : 1000 < center := by
  decide

theorem center_pos : 0 < center := by
  have := center_gt
  omega

theorem dvd_center {d : ℕ} (hd : 0 < d) (hd100 : d ≤ 100) : d ∣ center := by
  exact dvd_mul_of_dvd_left (Nat.dvd_factorial hd hd100) _

theorem center_even : center % 2 = 0 :=
  Nat.mod_eq_zero_of_dvd (dvd_center (by decide) (by decide))

theorem zero_window {x : ℕ} (hlo : center ≤ x + 100)
    (hhi : x ≤ center + 100) : 0 ∈ Nat.digits 10 x := by
  have hbase : (10 : ℕ) ^ 199 + 100 ≤ center := by decide
  have hlarge : (10 : ℕ) ^ 199 ≤ x := by omega
  have hlen : 199 < (Nat.digits 10 x).length :=
    (Nat.lt_digits_length_iff (by decide)).2 hlarge
  have hquot : x / 10 ^ 199 % 10 = 0 := by
    norm_num [center, Q, Nat.factorial] at hlo hhi ⊢
    omega
  have hget : (Nat.digits 10 x).getD 199 0 = 0 := by
    rw [Nat.getD_digits x 199 (by decide)]
    exact hquot
  rw [List.getD_eq_getElem _ _ hlen] at hget
  have hm : (Nat.digits 10 x)[199] ∈ Nat.digits 10 x := List.getElem_mem hlen
  rwa [hget] at hm

theorem left_window_coprime {e : ℕ} (he : e < center - 1)
    (hgap : center - 1 - e ≤ 99) : Nat.Coprime (center - 1) e := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpe
  have hpr : p ∣ center - 1 - e := Nat.dvd_sub hpa hpe
  have hrpos : 0 < center - 1 - e := by omega
  have hp100 : p ≤ 100 := by
    have := Nat.le_of_dvd hrpos hpr
    omega
  have hpc : p ∣ center := dvd_center hp.pos hp100
  have hpone : p ∣ center - (center - 1) := Nat.dvd_sub hpc hpa
  have hid : center - (center - 1) = 1 := by
    have := center_gt
    omega
  rwa [hid] at hpone

theorem right_window_coprime {e : ℕ} (he : e ≤ center)
    (hgap : center + 1 - e ≤ 99) : Nat.Coprime (center + 1) e := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpe
  have hpr : p ∣ center + 1 - e := Nat.dvd_sub hpa hpe
  have hrpos : 0 < center + 1 - e := by omega
  have hp100 : p ≤ 100 := by
    have := Nat.le_of_dvd hrpos hpr
    omega
  have hpc : p ∣ center := dvd_center hp.pos hp100
  have hpone : p ∣ center + 1 - center := Nat.dvd_sub hpa hpc
  simpa only [Nat.add_sub_cancel_left] using hpone

theorem coprime_near_center {e : ℕ} (_he : 0 < e)
    (hc : Nat.Coprime center e) (hd : Nat.dist center e < 100) :
    e = center - 1 ∨ e = center + 1 := by
  have hne : e ≠ center := by
    intro h
    have hone : center = 1 := by simpa [h, Nat.Coprime] using hc
    have := center_gt
    omega
  by_cases hle : e ≤ center
  · have hrpos : 0 < center - e := by omega
    have hsmall : center - e ≤ 100 := by
      rw [Nat.dist_eq_sub_of_le_right hle] at hd
      omega
    have hrc : center - e ∣ center := dvd_center hrpos hsmall
    have hre : center - e ∣ e := by
      have h := Nat.dvd_sub hrc (dvd_refl (center - e))
      have hid : center - (center - e) = e := by omega
      rwa [hid] at h
    have hone : center - e = 1 := Nat.eq_one_of_dvd_coprimes hc hrc hre
    left
    omega
  · have hrpos : 0 < e - center := by omega
    have hsmall : e - center ≤ 100 := by
      rw [Nat.dist_eq_sub_of_le (by omega : center ≤ e)] at hd
      omega
    have hrc : e - center ∣ center := dvd_center hrpos hsmall
    have hre : e - center ∣ e := by
      have h := Nat.dvd_add hrc (dvd_refl (e - center))
      have hid : center + (e - center) = e := by omega
      rwa [hid] at h
    have hone : e - center = 1 := Nat.eq_one_of_dvd_coprimes hc hrc hre
    right
    omega

end A380671Certificate


#print axioms A380671Certificate.center_gt
#print axioms A380671Certificate.center_even
#print axioms A380671Certificate.zero_window
#print axioms A380671Certificate.left_window_coprime
#print axioms A380671Certificate.right_window_coprime
#print axioms A380671Certificate.coprime_near_center
