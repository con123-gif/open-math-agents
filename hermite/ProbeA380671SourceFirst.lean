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

#print axioms A380671Certificate.canonical_isGreedy
#print axioms A380671Certificate.greedy_involution
#print axioms A380671Certificate.greedy_first
#print axioms A380671Certificate.greedy_second
#print axioms A380671Certificate.greedy_third
