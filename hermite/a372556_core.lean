namespace A372556Certificate
open OMA.S_oeis_a372556

@[simp] lemma value_zero : value 0 = 0 := rfl
@[simp] lemma value_add (a b : Multiset ℕ) : value (a + b) = value a + value b := by
  simp [value]
@[simp] lemma value_single (a : ℕ) : value {a} = jac a := by simp [value]
@[simp] lemma value_replicate (k a : ℕ) : value (Multiset.replicate k a) = k * jac a := by
  simp [value, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

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

lemma even_quad {i : ℕ} (hi : i % 2 = 0) : jac (i + 2) = 4 * jac i + 1 := by
  have h := (alt_step i).1 hi
  have hr : jac (i + 2) = jac (i + 1) + 2 * jac i := rfl
  omega

lemma jac_mono : Monotone jac := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => norm_num [jac]
  | succ n =>
    change jac (n + 1) ≤ jac (n + 1) + 2 * jac n
    omega

lemma jac_pos {i : ℕ} (hi : 1 ≤ i) : 0 < jac i := by
  have h := jac_mono hi
  norm_num [jac] at h
  omega

lemma jac_strict {i : ℕ} (hi : 2 ≤ i) : jac i < jac (i + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hp := jac_pos (i := j + 1) (by omega)
  have hh : jac (j + 2) < jac (j + 3) := by
    have hr : jac (j + 3) = jac (j + 2) + 2 * jac (j + 1) := rfl
    omega
  convert hh using 1 <;> congr 1 <;> omega

lemma index_le (i : ℕ) : i ≤ jac i + 1 := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases h : i < 2
    · interval_cases i <;> norm_num [jac]
    · have hs := jac_strict (i := i) (by omega)
      omega

lemma member_value_le {m : Multiset ℕ} {i : ℕ} (hi : i ∈ m) : jac i ≤ value m := by
  exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) (jac i)
    (Multiset.mem_map.mpr ⟨i, hi, rfl⟩)

lemma represents_bound {n : ℕ} {m : Multiset ℕ} (hm : represents n m) {i : ℕ}
    (hi : i ∈ m) : i ≤ n + 1 := by
  have hv := member_value_le hi
  have hin := index_le i
  rw [hm.2] at hv
  omega

lemma represents_ones (n : ℕ) : represents n (Multiset.replicate n 2) := by
  constructor
  · intro i hi
    have he : i = 2 := (Multiset.mem_replicate.mp hi).2
    omega
  · simp [jac]

lemma exists_optimal (n : ℕ) : ∃ m, optimal n m := by
  classical
  let P : ℕ → Prop := fun k => ∃ m, represents n m ∧ m.card = k
  have hP : ∃ k, P k := ⟨n, Multiset.replicate n 2, represents_ones n, by simp⟩
  obtain ⟨m, hm, hcard⟩ := Nat.find_spec hP
  refine ⟨m, hm, ?_⟩
  intro r hr
  rw [hcard]
  exact Nat.find_min' hP ⟨r, hr, rfl⟩

def score (m : Multiset ℕ) : ℕ := (m.map fun i => 5 ^ i).sum
@[simp] lemma score_zero : score 0 = 0 := rfl
@[simp] lemma score_add (a b : Multiset ℕ) : score (a + b) = score a + score b := by
  simp [score]
@[simp] lemma score_single (a : ℕ) : score {a} = 5 ^ a := by simp [score]
@[simp] lemma score_replicate (k a : ℕ) : score (Multiset.replicate k a) = k * 5 ^ a := by
  simp [score, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

lemma score_bound {n : ℕ} {m : Multiset ℕ} (hm : represents n m) (hc : m.card ≤ n) :
    score m ≤ n * 5 ^ (n + 1) := by
  have hx : ∀ x ∈ m.map (fun i => 5 ^ i), x ≤ 5 ^ (n + 1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact Nat.pow_le_pow_right (by omega) (represents_bound hm hi)
  have hs := Multiset.sum_le_card_nsmul (m.map fun i => 5 ^ i) (5 ^ (n + 1)) hx
  simp only [Multiset.card_map, nsmul_eq_mul] at hs
  exact hs.trans (Nat.mul_le_mul_right _ hc)

def best (n : ℕ) (m : Multiset ℕ) : Prop :=
  optimal n m ∧ ∀ r, represents n r → r.card ≤ m.card → score r ≤ score m

lemma exists_best (n : ℕ) : ∃ m, best n m := by
  classical
  obtain ⟨m, hm⟩ := exists_optimal n
  have hmn : m.card ≤ n := by
    simpa using hm.2 _ (represents_ones n)
  let P : ℕ → Prop := fun s => ∃ r, represents n r ∧ r.card ≤ m.card ∧ score r = s
  have hp : P (score m) := ⟨m, hm.1, le_rfl, rfl⟩
  have hs := score_bound hm.1 hmn
  obtain ⟨r, hr, hrc, hscore⟩ := Nat.findGreatest_spec hs hp
  refine ⟨r, ⟨hr, ?_⟩, ?_⟩
  · intro t ht
    exact hrc.trans (hm.2 t ht)
  · intro t ht htc
    by_contra hh
    have hts : Nat.findGreatest P (n * 5 ^ (n + 1)) < score t := by omega
    have htn : t.card ≤ n := htc.trans (hrc.trans hmn)
    have htsb := score_bound ht htn
    have htp : P (score t) := ⟨t, ht, htc.trans hrc, rfl⟩
    exact Nat.findGreatest_is_greatest hts htsb htp

lemma replacement_impossible {n : ℕ} {m old new : Multiset ℕ}
    (hm : best n m) (hle : old ≤ m) (hnew : ∀ i ∈ new, 2 ≤ i)
    (hv : value old = value new) (hc : new.card ≤ old.card)
    (hs : score old < score new) : False := by
  obtain ⟨r, hr⟩ := Multiset.le_iff_exists_add.mp hle
  have hrep : represents n (new + r) := by
    constructor
    · intro i hi
      rcases Multiset.mem_add.mp hi with hi | hi
      · exact hnew i hi
      · apply hm.1.1.1 i
        rw [hr]
        exact Multiset.mem_add.mpr (Or.inr hi)
    · have hn := hm.1.1.2
      rw [hr, value_add, hv] at hn
      simpa using hn
  have hcard : (new + r).card ≤ m.card := by
    rw [hr]
    simp only [Multiset.card_add]
    omega
  have hb := hm.2 _ hrep hcard
  rw [hr, score_add, score_add] at hb
  omega

end A372556Certificate
