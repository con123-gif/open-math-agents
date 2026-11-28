import Mathlib

/-!
OEIS A380671, revision 11 (January 31, 2025), by David James Sycamore
and Michael De Vlieger: https://oeis.org/A380671.
At each positive row n, choose the least unused positive integer coprime
to n and sharing an actual decimal digit with n. The conjecture combines
permutation of the positive integers and displacement strictly below 100.
The source's unmarked self-inverse formula is prior mathematics; the
disproof concerns the displacement clause. Nat.digits omits leading zeros.
Index zero is a dummy value and is excluded from every source assertion.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex,
GPT-6 (exact serving variant not exposed).
-/

namespace OMA.S_oeis_a380671

def sharesDigit (n m : ℕ) : Prop :=
  ((Nat.digits 10 n).toFinset ∩ (Nat.digits 10 m).toFinset).Nonempty

def admissible (n m : ℕ) : Prop :=
  0 < m ∧ Nat.Coprime n m ∧ sharesDigit n m

noncomputable def next (n : ℕ) (used : Finset ℕ) : ℕ :=
  sInf {m : ℕ | admissible n m ∧ m ∉ used}

noncomputable def state : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (next (n + 1) (state n)) (state n)

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else next n (state (n - 1))

def conjecture : Prop :=
  Set.BijOn a (Set.Ioi 0) (Set.Ioi 0) ∧
    ∀ n : ℕ, 0 < n → Nat.dist n (a n) < 100


end OMA.S_oeis_a380671

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/- Canonical least-unused construction and generic symmetric greedy involution.
   Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex,
   GPT-6 (exact serving variant not exposed). Source self-inversion is prior.
   Candidate source: not claimed compiler-verified until an actual run. -/

namespace A380671Certificate

open OMA.S_oeis_a380671

theorem sharesDigit_comm (n m : ℕ) : sharesDigit n m ↔ sharesDigit m n := by
  simp only [sharesDigit, Finset.inter_comm]

theorem admissible_symm {n m : ℕ} (hn : 0 < n) (h : admissible n m) :
    admissible m n :=
  ⟨hn, h.2.1.symm, (sharesDigit_comm n m).mp h.2.2⟩

theorem candidate_above (n M : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, M < m ∧ admissible n m := by
  let m := 1 + 10 ^ (M + 2) * n
  have hp : M + 2 < 10 ^ (M + 2) := Nat.lt_pow_self (by decide)
  have hmul : 10 ^ (M + 2) ≤ 10 ^ (M + 2) * n :=
    Nat.le_mul_of_pos_right _ hn
  have hm : M < m := by dsimp [m]; omega
  have hd : Nat.digits 10 1 ++ List.replicate (M + 1) 0 ++ Nat.digits 10 n =
      Nat.digits 10 m := by
    have he := Nat.digits_append_zeroes_append_digits
      (b := 10) (k := M + 1) (m := n) (n := 1) (by decide) hn
    have hlen : (Nat.digits 10 1).length = 1 := by decide
    simpa only [hlen, show 1 + (M + 1) = M + 2 by omega] using he
  obtain ⟨d, hdmem⟩ := List.exists_mem_of_ne_nil (Nat.digits 10 n)
    (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))
  have hdm : d ∈ Nat.digits 10 m := by
    rw [← hd]
    exact List.mem_append_right _ hdmem
  refine ⟨m, hm, by omega, ?_, ?_⟩
  · dsimp [m]
    exact (Nat.coprime_add_mul_right_right n 1 (10 ^ (M + 2))).mpr (by simp)
  · exact ⟨d, Finset.mem_inter.mpr ⟨by simpa using hdmem, by simpa using hdm⟩⟩

theorem candidates_nonempty (n : ℕ) (used : Finset ℕ) (hn : 0 < n) :
    {m : ℕ | admissible n m ∧ m ∉ used}.Nonempty := by
  obtain ⟨m, hm, hadm⟩ := candidate_above n (used.sup id) hn
  refine ⟨m, hadm, ?_⟩
  intro hin
  have hle : m ≤ used.sup id := Finset.le_sup (f := id) hin
  omega

theorem next_spec (n : ℕ) (used : Finset ℕ) (hn : 0 < n) :
    admissible n (next n used) ∧ next n used ∉ used := by
  exact csInf_mem (candidates_nonempty n used hn)

theorem next_le {n m : ℕ} {used : Finset ℕ}
    (hm : admissible n m) (hu : m ∉ used) : next n used ≤ m :=
  csInf_le (OrderBot.bddBelow _) ⟨hm, hu⟩

theorem a_eq {n : ℕ} (hn : 0 < n) : a n = next n (state (n - 1)) := by
  simp only [a, if_neg (by omega : n ≠ 0)]

theorem state_succ (n : ℕ) : state (n + 1) = insert (a (n + 1)) (state n) := by
  simp only [state, a, show n + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]

theorem state_eq_image (n : ℕ) :
    state n = (Finset.range n).image (fun i => a (i + 1)) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state_succ, ih, Finset.range_succ, Finset.image_insert]

theorem mem_state_iff (n m : ℕ) :
    m ∈ state n ↔ ∃ i : ℕ, 0 < i ∧ i ≤ n ∧ a i = m := by
  rw [state_eq_image]
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact ⟨i + 1, by omega, by have hi' := Finset.mem_range.mp hi; omega, he⟩
  · rintro ⟨i, hi, hin, he⟩
    apply Finset.mem_image.mpr
    refine ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using he

structure IsGreedy (f : ℕ → ℕ) : Prop where
  valid : ∀ n : ℕ, 0 < n → admissible n (f n)
  fresh : ∀ i n : ℕ, 0 < i → i < n → f i ≠ f n
  least : ∀ n m : ℕ, 0 < n → admissible n m →
    (∀ i : ℕ, 0 < i → i < n → f i ≠ m) → f n ≤ m

theorem canonical_isGreedy : IsGreedy a := by
  constructor
  · intro n hn
    rw [a_eq hn]
    exact (next_spec n _ hn).1
  · intro i n hi hin he
    have hn : 0 < n := by omega
    have hnot : a n ∉ state (n - 1) := by
      rw [a_eq hn]
      exact (next_spec n _ hn).2
    apply hnot
    exact (mem_state_iff _ _).mpr ⟨i, hi, by omega, he⟩
  · intro n m hn hm hu
    rw [a_eq hn]
    apply next_le hm
    intro hs
    obtain ⟨i, hi, hin, he⟩ := (mem_state_iff _ _).mp hs
    exact hu i hi (by omega) he

theorem greedy_injective {f : ℕ → ℕ} (hf : IsGreedy f)
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (he : f i = f j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hf.fresh i j hi hlt he
  · exact hf.fresh j i hj hgt he.symm

theorem greedy_involution {f : ℕ → ℕ} (hf : IsGreedy f) :
    ∀ n : ℕ, 0 < n → f (f n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    let j := f n
    have hj : 0 < j := (hf.valid n hn).1
    change f j = n
    rcases lt_trichotomy j n with hlt | heq | hgt
    · have hi := ih j hlt hj
      have hp : 0 < f j := (hf.valid j hj).1
      apply greedy_injective hf hp hn
      exact hi
    · calc
        f j = f n := congrArg f heq
        _ = j := rfl
        _ = n := heq
    · have hun : ∀ i : ℕ, 0 < i → i < j → f i ≠ n := by
        intro i hi hij hei
        rcases lt_trichotomy i n with hin | hie | hni
        · have hfix := ih i hin hi
          rw [hei] at hfix
          change j = i at hfix
          omega
        · subst i
          change j = n at hei
          omega
        · have hfree : ∀ h : ℕ, 0 < h → h < n → f h ≠ i := by
            intro h hh hhn hehi
            have hfix := ih h hhn hh
            rw [hehi, hei] at hfix
            omega
          have hadm : admissible n i := admissible_symm hn (by
            simpa only [hei] using hf.valid i hi)
          have hleast := hf.least n i hn hadm hfree
          change j ≤ i at hleast
          omega
      have hjn : f j ≤ n := hf.least j n hj
        (admissible_symm hn (hf.valid n hn)) hun
      apply Nat.le_antisymm hjn
      by_contra hbad
      have hbn : f j < n := by omega
      have hb : 0 < f j := (hf.valid j hj).1
      have hib := ih (f j) hbn hb
      have hpos : 0 < f (f j) := (hf.valid (f j) hb).1
      have hab : f (f j) = j := greedy_injective hf hpos hj hib
      have hfresh := hf.fresh (f j) n hb hbn
      exact hfresh hab

theorem greedy_first {f : ℕ → ℕ} (hf : IsGreedy f) : f 1 = 1 := by
  have hup : f 1 ≤ 1 := hf.least 1 1 (by decide)
    (by decide) (by intro i hi hil; omega)
  have hpos := (hf.valid 1 (by decide)).1
  omega

theorem greedy_second {f : ℕ → ℕ} (hf : IsGreedy f) : f 2 = 21 := by
  have h1 := greedy_first hf
  have hup : f 2 ≤ 21 := hf.least 2 21 (by decide) (by decide) (by
    intro i hi hil
    have he : i = 1 := by omega
    simpa [he, h1])
  have hlo : ∀ m : Fin 21, 0 < m.val → ¬ admissible 2 m.val := by decide
  have hvalid := hf.valid 2 (by decide)
  by_contra hne
  have hlt : f 2 < 21 := by omega
  exact hlo ⟨f 2, hlt⟩ hvalid.1 hvalid

theorem greedy_third {f : ℕ → ℕ} (hf : IsGreedy f) : f 3 = 13 := by
  have h1 := greedy_first hf
  have h2 := greedy_second hf
  have hup : f 3 ≤ 13 := hf.least 3 13 (by decide) (by decide) (by
    intro i hi hil
    have he : i = 1 ∨ i = 2 := by omega
    rcases he with he | he
    · simpa [he, h1]
    · simpa [he, h2])
  have hlo : ∀ m : Fin 13, 0 < m.val → ¬ admissible 3 m.val := by decide
  have hvalid := hf.valid 3 (by decide)
  by_contra hne
  have hlt : f 3 < 13 := by omega
  exact hlo ⟨f 3, hlt⟩ hvalid.1 hvalid

end A380671Certificate


/-!
Pure finite parity-counting infrastructure for A380671.
The hypotheses here are to be proved from the literal greedy rule by the
main certificate. This file assumes no bounded-displacement conjecture.
Local candidate, not yet checked by the pinned Lean verifier.
Credit: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed.
-/

namespace A380671Certificate

theorem parity_even_image_mod (a : ℕ → ℕ)
    (cop : ∀ n, 0 < n → Nat.Coprime n (a n)) (i : ℕ) :
    a (2 * (i + 1)) % 2 = 1 := by
  have hepos : 0 < 2 * (i + 1) := by omega
  have hc := cop (2 * (i + 1)) hepos
  change Nat.gcd (2 * (i + 1)) (a (2 * (i + 1))) = 1 at hc
  by_contra h
  have hm : a (2 * (i + 1)) % 2 = 0 := by omega
  have hd₁ : 2 ∣ 2 * (i + 1) := ⟨i + 1, rfl⟩
  have hd₂ : 2 ∣ a (2 * (i + 1)) := Nat.dvd_of_mod_eq_zero hm
  have hg := Nat.dvd_gcd hd₁ hd₂
  rw [hc] at hg
  norm_num at hg

theorem parity_even_image_ge_five (a : ℕ → ℕ)
    (pos : ∀ n, 0 < n → 0 < a n)
    (cop : ∀ n, 0 < n → Nat.Coprime n (a n))
    (inv : ∀ n, 0 < n → a (a n) = n)
    (a1 : a 1 = 1) (a3 : a 3 = 13) (i : ℕ) :
    5 ≤ a (2 * (i + 1)) := by
  have hepos : 0 < 2 * (i + 1) := by omega
  have hp := pos (2 * (i + 1)) hepos
  have ho := parity_even_image_mod a cop i
  have hn1 : a (2 * (i + 1)) ≠ 1 := by
    intro h
    have hv := inv (2 * (i + 1)) hepos
    rw [h, a1] at hv
    omega
  have hn3 : a (2 * (i + 1)) ≠ 3 := by
    intro h
    have hv := inv (2 * (i + 1)) hepos
    rw [h, a3] at hv
    omega
  omega

theorem parity_even_image_index_injective (a : ℕ → ℕ)
    (inv : ∀ n, 0 < n → a (a n) = n) (i j : ℕ)
    (h : a (2 * (i + 1)) = a (2 * (j + 1))) : i = j := by
  have hh := congrArg a h
  rw [inv (2 * (i + 1)) (by omega), inv (2 * (j + 1)) (by omega)] at hh
  omega

theorem two_even_escape (a : ℕ → ℕ)
    (pos : ∀ n, 0 < n → 0 < a n)
    (cop : ∀ n, 0 < n → Nat.Coprime n (a n))
    (inv : ∀ n, 0 < n → a (a n) = n)
    (a1 : a 1 = 1) (a3 : a 3 = 13)
    (T : ℕ) (hT : 4 ≤ T) (hEven : T % 2 = 0) :
    ∃ e f, 0 < e ∧ e ≤ T ∧ e % 2 = 0 ∧ T < a e ∧
      0 < f ∧ f ≤ T ∧ f % 2 = 0 ∧ T < a f ∧ e ≠ f := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, T = 2 * m := ⟨T / 2, by omega⟩
  have hm : 2 ≤ m := by omega
  let escapes : Fin m → Prop := fun i => 2 * m < a (2 * (i.val + 1))
  have hdata (i : Fin m) (hi : ¬ escapes i) :
      5 ≤ a (2 * (i.val + 1)) ∧ a (2 * (i.val + 1)) ≤ 2 * m ∧
        a (2 * (i.val + 1)) % 2 = 1 := by
    refine ⟨parity_even_image_ge_five a pos cop inv a1 a3 i.val, ?_,
      parity_even_image_mod a cop i.val⟩
    change ¬ 2 * m < a (2 * (i.val + 1)) at hi
    omega
  have hpairs : ∃ i j : Fin m, escapes i ∧ escapes j ∧ i ≠ j := by
    by_contra hnone
    have hunique (i j : Fin m) (hi : escapes i) (hj : escapes j) : i = j := by
      by_contra hij
      exact hnone ⟨i, j, hi, hj, hij⟩
    -- Internal even labels have distinct odd images in {5,7,...,2m-1},
    -- a set of size m-2. At most one escaping label gets the extra None.
    let code : Fin m → Option (Fin (m - 2)) := fun i =>
      if hi : escapes i then none
      else some ⟨(a (2 * (i.val + 1)) - 5) / 2, by
        rcases hdata i hi with ⟨hlo, hhi, hodd⟩
        omega⟩
    have hcode : Function.Injective code := by
      intro i j hij
      by_cases hi : escapes i
      · by_cases hj : escapes j
        · exact hunique i j hi hj
        · simp [code, hi, hj] at hij
      · by_cases hj : escapes j
        · simp [code, hi, hj] at hij
        · have hquot : (a (2 * (i.val + 1)) - 5) / 2 =
              (a (2 * (j.val + 1)) - 5) / 2 := by
            simpa [code, hi, hj] using hij
          rcases hdata i hi with ⟨hloi, hhii, hoddi⟩
          rcases hdata j hj with ⟨hloj, hhij, hoddj⟩
          have haeq : a (2 * (i.val + 1)) = a (2 * (j.val + 1)) := by omega
          apply Fin.ext
          exact parity_even_image_index_injective a inv i.val j.val haeq
    have hc := Fintype.card_le_of_injective code hcode
    simp only [Fintype.card_fin, Fintype.card_option] at hc
    omega
  obtain ⟨i, j, hi, hj, hne⟩ := hpairs
  change 2 * m < a (2 * (i.val + 1)) at hi
  change 2 * m < a (2 * (j.val + 1)) at hj
  have hil := i.isLt
  have hjl := j.isLt
  refine ⟨2 * (i.val + 1), 2 * (j.val + 1), by omega, by omega,
    by omega, hi, by omega, by omega, by omega, hj, ?_⟩
  intro heq
  apply hne
  apply Fin.ext
  omega

end A380671Certificate



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



/- Full displacement obstruction for the exact canonical A380671 sequence.
   This fragment depends on the separately compiled source, parity, and
   arithmetic-window helpers. No kernel pass is asserted by this comment.
   Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex,
   GPT-6 (exact serving variant not exposed). -/

namespace A380671Certificate

open OMA.S_oeis_a380671

theorem shares_of_zero {n m : ℕ} (hn : 0 ∈ Nat.digits 10 n)
    (hm : 0 ∈ Nat.digits 10 m) : sharesDigit n m := by
  exact ⟨0, Finset.mem_inter.mpr ⟨by simpa using hn, by simpa using hm⟩⟩

theorem uniform_bound_false :
    ¬ (∀ n : ℕ, 0 < n → Nat.dist n (a n) < 100) := by
  intro hb
  have hg := canonical_isGreedy
  have hinv := greedy_involution hg
  have hpos : ∀ n : ℕ, 0 < n → 0 < a n := fun n hn => (hg.valid n hn).1
  have hcop : ∀ n : ℕ, 0 < n → Nat.Coprime n (a n) :=
    fun n hn => (hg.valid n hn).2.1
  have h1 := greedy_first hg
  have h3 := greedy_third hg
  have hc := center_gt
  have hcenter : 0 < center := by omega
  have hleftrow : 0 < center - 1 := by omega
  have hrightrow : 0 < center + 1 := by omega
  have hchoices : a center = center - 1 ∨ a center = center + 1 :=
    coprime_near_center (hpos center hcenter) (hcop center hcenter) (hb center hcenter)
  have hnotleft : a center ≠ center - 1 := by
    intro hleft
    have hmate : a (center - 1) = center := by
      have hi := hinv center hcenter
      rwa [hleft] at hi
    have hTeven : (center - 2) % 2 = 0 := by
      have he := center_even
      omega
    obtain ⟨e, f, hepos, heT, heeven, heescape,
      hfpos, hfT, hfeven, hfescape, hef⟩ :=
      two_even_escape a hpos hcop hinv h1 h3 (center - 2) (by omega) hTeven
    have helt : e < center - 1 := by omega
    have hgap : center - 1 - e ≤ 99 := by
      have hd := hb e hepos
      unfold Nat.dist at hd
      omega
    have hezero : 0 ∈ Nat.digits 10 e := zero_window (by omega) (by omega)
    have hnzero : 0 ∈ Nat.digits 10 (center - 1) :=
      zero_window (by omega) (by omega)
    have hadm : admissible (center - 1) e :=
      ⟨hepos, left_window_coprime helt hgap, shares_of_zero hnzero hezero⟩
    have hunused : ∀ i : ℕ, 0 < i → i < center - 1 → a i ≠ e := by
      intro i hi hil hei
      have hiinv := hinv i hi
      rw [hei] at hiinv
      omega
    have hleast := hg.least (center - 1) e hleftrow hadm hunused
    rw [hmate] at hleast
    omega
  have hright : a center = center + 1 := hchoices.resolve_left hnotleft
  have hmate : a (center + 1) = center := by
    have hi := hinv center hcenter
    rwa [hright] at hi
  obtain ⟨e, f, hepos, heT, heeven, heescape,
    hfpos, hfT, hfeven, hfescape, hef⟩ :=
    two_even_escape a hpos hcop hinv h1 h3 center (by omega) center_even
  have hex : ∃ u : ℕ, 0 < u ∧ u < center ∧ center < a u := by
    by_cases hec : e = center
    · refine ⟨f, hfpos, ?_, hfescape⟩
      have hfc : f ≠ center := by intro hfc; exact hef (hec.trans hfc.symm)
      omega
    · exact ⟨e, hepos, by omega, heescape⟩
  obtain ⟨u, hupos, hult, huescape⟩ := hex
  have hgap : center + 1 - u ≤ 99 := by
    have hd := hb u hupos
    unfold Nat.dist at hd
    omega
  have huzero : 0 ∈ Nat.digits 10 u := zero_window (by omega) (by omega)
  have hnzero : 0 ∈ Nat.digits 10 (center + 1) :=
    zero_window (by omega) (by omega)
  have hadm : admissible (center + 1) u :=
    ⟨hupos, right_window_coprime (by omega) hgap, shares_of_zero hnzero huzero⟩
  have hunused : ∀ i : ℕ, 0 < i → i < center + 1 → a i ≠ u := by
    intro i hi hil hei
    have hiinv := hinv i hi
    rw [hei] at hiinv
    omega
  have hleast := hg.least (center + 1) u hrightrow hadm hunused
  rw [hmate] at hleast
  omega

end A380671Certificate

theorem OMA.disproof : ¬ OMA.S_oeis_a380671.conjecture := by
  intro h
  exact A380671Certificate.uniform_bound_false h.2

#print axioms A380671Certificate.canonical_isGreedy
#print axioms A380671Certificate.greedy_involution
#print axioms A380671Certificate.two_even_escape
#print axioms A380671Certificate.zero_window
#print axioms A380671Certificate.uniform_bound_false
#print axioms OMA.disproof
