import Mathlib

/-! Helper for MO474511. Candidate, not yet kernel verified. -/
namespace OMA.MO474511

open Filter Topology
open scoped NNReal BigOperators Matrix.Norms.Elementwise

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def commRight {n : ℕ} (x : Mat n) : Mat n →ₗ[ℝ] Mat n where
  toFun y := y * x - x * y
  map_add' y z := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
  map_smul' c y := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply]

/-- Right test matrices whose commutators with the curve have bounded norm. -/
def boundedTests {n : ℕ} (A : ℝ≥0 → Mat n) : Submodule ℝ (Mat n) where
  carrier := {x | ∃ C : ℝ, ∀ t, ‖A t * x - x * A t‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun t => ?_⟩
    have h : A t * (x + y) - (x + y) * A t =
        (A t * x - x * A t) + (A t * y - y * A t) := by
      simp only [Matrix.mul_add, Matrix.add_mul]; abel
    rw [h]
    exact (norm_add_le _ _).trans (add_le_add (hC t) (hD t))
  smul_mem' := by
    rintro c x ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun t => ?_⟩
    have h : A t * (c • x) - (c • x) * A t =
        c • (A t * x - x * A t) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [h, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg c)

/-- Uniformly bounded commutators imply boundedness modulo the center of the
linear span of the curve. No boundedness of the original curve is assumed. -/
theorem bounded_mod_center {n : ℕ} (A : ℝ≥0 → Mat n)
    (hA : Continuous A)
    (hcomm : ∀ s t, ‖A t * A s - A s * A t‖ ≤ 1) :
    ∃ Zm : Submodule ℝ (Mat n),
      (∀ x ∈ Zm, ∀ y ∈ Zm, x * y = y * x) ∧
      ∃ z b : ℝ≥0 → Mat n,
        Continuous z ∧ Continuous b ∧
        (∀ t, z t ∈ Zm) ∧
        (∀ t, z t + b t = A t) ∧
        (∀ x ∈ Zm, ∀ t, x * b t = b t * x) ∧
        Bornology.IsBounded (Set.range b) := by
  classical
  let V := Submodule.span ℝ (Set.range A)
  let Av : ℝ≥0 → V := fun t => ⟨A t, Submodule.subset_span ⟨t, rfl⟩⟩
  have hAv : Continuous Av := hA.subtype_mk _
  have htests : V ≤ boundedTests A := by
    apply Submodule.span_le.mpr
    rintro x ⟨s, rfl⟩
    exact ⟨1, fun t => hcomm s t⟩
  let basis := Module.finBasis ℝ V
  let F : V →ₗ[ℝ] (Fin (Module.finrank ℝ V) → Mat n) :=
    LinearMap.pi fun i => (commRight (basis i : Mat n)).comp V.subtype
  let Z := LinearMap.ker F
  have hcentral (z : V) (hz : z ∈ Z) (v : V) :
      (z : Mat n) * (v : Mat n) = (v : Mat n) * (z : Mat n) := by
    have hzF : F z = 0 := hz
    let g : V →ₗ[ℝ] Mat n := (commRight (z : Mat n)).comp V.subtype
    have hg : g = 0 := by
      apply basis.ext
      intro i
      have hi : (z : Mat n) * (basis i : Mat n) -
          (basis i : Mat n) * (z : Mat n) = 0 := by
        simpa [F, commRight] using congrFun hzF i
      change (basis i : Mat n) * (z : Mat n) -
        (z : Mat n) * (basis i : Mat n) = 0
      exact sub_eq_zero.mpr (sub_eq_zero.mp hi).symm
    have hv : (v : Mat n) * (z : Mat n) - (z : Mat n) * (v : Mat n) = 0 := by
      simpa [g, commRight] using LinearMap.congr_fun hg v
    exact (sub_eq_zero.mp hv).symm
  obtain ⟨L, hZL⟩ := Z.exists_isCompl
  let pZ : V →ₗ[ℝ] V := Z.projection L hZL
  let pL : V →ₗ[ℝ] V := L.projection Z hZL.symm
  have hsplit (v : V) : pZ v + pL v = v := by
    exact Submodule.projection_add_projection_eq_self hZL v
  have hFproj (v : V) : F (pL v) = F v := by
    have hz : F (pZ v) = 0 := by
      exact Submodule.projection_apply_mem hZL v
    calc
      F (pL v) = F (pZ v) + F (pL v) := by rw [hz]; simp
      _ = F (pZ v + pL v) := (F.map_add _ _).symm
      _ = F v := congrArg F (hsplit v)
  let FL := F.comp L.subtype
  have hFL : Function.Injective FL := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxZ : (x : V) ∈ Z := hx
    have hx0 : (x : V) = 0 :=
      (Submodule.disjoint_def.mp hZL.disjoint) _ hxZ x.property
    simpa only [Submodule.mem_bot] using Subtype.ext hx0
  obtain ⟨K, _, hK⟩ := FL.injective_iff_antilipschitz.mp hFL
  have htest (i : Fin (Module.finrank ℝ V)) :
      ∃ C : ℝ, ∀ t, ‖(F (Av t)) i‖ ≤ C := by
    simpa [F, Av, commRight, boundedTests] using htests (basis i).property
  choose C hC using htest
  let D : ℝ := ∑ i, max (C i) 0
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hFbound (t : ℝ≥0) : ‖F (Av t)‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro i
    exact (hC i t).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)))
  let zmap : V →ₗ[ℝ] Mat n := V.subtype.comp pZ
  let bmap : V →ₗ[ℝ] Mat n := V.subtype.comp pL
  let z := zmap ∘ Av
  let b := bmap ∘ Av
  let Zm : Submodule ℝ (Mat n) := Z.map V.subtype
  refine ⟨Zm, ?_, z, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    exact hcentral u hu v
  · exact zmap.continuous_of_finiteDimensional.comp hAv
  · exact bmap.continuous_of_finiteDimensional.comp hAv
  · intro t
    exact ⟨pZ (Av t), Submodule.projection_apply_mem hZL _, rfl⟩
  · intro t
    exact congrArg (fun v : V => (v : Mat n)) (hsplit (Av t))
  · rintro x ⟨u, hu, rfl⟩ t
    exact hcentral u hu (pL (Av t))
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(K : ℝ) * D, ?_⟩
    rintro x ⟨t, rfl⟩
    let l : L := ⟨pL (Av t), Submodule.projection_apply_mem hZL.symm _⟩
    have hl := ZeroHomClass.bound_of_antilipschitz FL hK l
    have hFl : FL l = F (Av t) := hFproj _
    change ‖(l : V)‖ ≤ (K : ℝ) * D
    calc
      ‖(l : V)‖ ≤ (K : ℝ) * ‖FL l‖ := hl
      _ = (K : ℝ) * ‖F (Av t)‖ := by rw [hFl]
      _ ≤ (K : ℝ) * D := mul_le_mul_of_nonneg_left (hFbound t) K.coe_nonneg

end OMA.MO474511

#print axioms OMA.MO474511.bounded_mod_center
