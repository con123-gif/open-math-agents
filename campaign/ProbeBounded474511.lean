import Mathlib

/-! The bounded residual step in MO474511. Candidate, not yet kernel verified. -/
namespace OMA.MO474511.Bounded

open Filter Topology
open scoped NNReal Matrix.Norms.Elementwise

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def commRight {n : ℕ} (z : Mat n) : Mat n →ₗ[ℝ] Mat n where
  toFun x := x * z - z * x
  map_add' x y := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
  map_smul' c x := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply]

def clusterSpan {n : ℕ} (b : ℝ≥0 → Mat n) : Submodule ℝ (Mat n) :=
  Submodule.span ℝ {x | MapClusterPt x atTop b}

theorem commutes_span {n : ℕ} {S : Set (Mat n)} {z : Mat n}
    (hS : ∀ x ∈ S, z * x = x * z) :
    ∀ x ∈ Submodule.span ℝ S, z * x = x * z := by
  have hker : Submodule.span ℝ S ≤ LinearMap.ker (commRight z) := by
    apply Submodule.span_le.mpr
    intro x hx
    change x * z - z * x = 0
    exact sub_eq_zero.mpr (hS x hx).symm
  intro x hx
  have h : x * z - z * x = 0 := hker hx
  exact (sub_eq_zero.mp h).symm

theorem abelian_span {n : ℕ} {S : Set (Mat n)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S,
      x * y = y * x := by
  have hgen : ∀ x ∈ S, ∀ y ∈ Submodule.span ℝ S, x * y = y * x := by
    intro x hx
    exact commutes_span (hS x hx)
  intro x hx y hy
  exact (commutes_span (fun z hz => (hgen z hz y hy).symm) x hx).symm

theorem clusters_commute {n : ℕ} (b : ℝ≥0 → Mat n)
    (hcomm : Tendsto (fun p : ℝ≥0 × ℝ≥0 => b p.1 * b p.2 - b p.2 * b p.1)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∀ x, MapClusterPt x atTop b → ∀ y, MapClusterPt y atTop b →
      x * y = y * x := by
  intro x hx y hy
  have hxy : MapClusterPt (x, y) (atTop ×ˢ atTop) (Prod.map b b) :=
    hx.prodMap hy
  have hcont : Continuous (fun p : Mat n × Mat n => p.1 * p.2 - p.2 * p.1) :=
    (continuous_fst.mul continuous_snd).sub (continuous_snd.mul continuous_fst)
  have hc : MapClusterPt (x * y - y * x) (atTop ×ˢ atTop)
      (fun p : ℝ≥0 × ℝ≥0 => b p.1 * b p.2 - b p.2 * b p.1) :=
    hxy.continuousAt_comp hcont.continuousAt
  have hz : ClusterPt (x * y - y * x) (𝓝 (0 : Mat n)) :=
    hc.clusterPt.mono hcomm
  exact sub_eq_zero.mp (inseparable_iff_eq.mp (Inseparable.of_nhds_neBot hz))

theorem clusterSpan_abelian {n : ℕ} (b : ℝ≥0 → Mat n)
    (hcomm : Tendsto (fun p : ℝ≥0 × ℝ≥0 => b p.1 * b p.2 - b p.2 * b p.1)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∀ x ∈ clusterSpan b, ∀ y ∈ clusterSpan b, x * y = y * x :=
  abelian_span (clusters_commute b hcomm)

/-- Every fixed matrix commuting with the whole residual curve commutes with
its cluster span. -/
theorem clusterSpan_centralizes {n : ℕ} (b : ℝ≥0 → Mat n) (z : Mat n)
    (hz : ∀ t, z * b t = b t * z) :
    ∀ x ∈ clusterSpan b, z * x = x * z := by
  apply commutes_span
  intro x hx
  have hclosed : IsClosed {y : Mat n | z * y = y * z} :=
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  exact hclosed.mem_of_mapClusterPt hx (Filter.Eventually.of_forall hz)

/-- A continuous linear map vanishing on the cluster span sends a bounded
curve to zero. This is the compactness step attributed to Benoist in the source. -/
theorem tendsto_zero_of_vanish {n : ℕ} (b : ℝ≥0 → Mat n)
    (hb : Bornology.IsBounded (Set.range b)) (D : Mat n →ₗ[ℝ] Mat n)
    (hD : ∀ x ∈ clusterSpan b, D x = 0) :
    Tendsto (fun t => D (b t)) atTop (𝓝 0) := by
  have hcompact : IsCompact (closure (Set.range b)) := hb.isCompact_closure
  have hmem : ∀ᶠ t in atTop, b t ∈ closure (Set.range b) :=
    Filter.Eventually.of_forall fun t => subset_closure ⟨t, rfl⟩
  have hnear : Tendsto b atTop (𝓝ˢ (clusterSpan b : Set (Mat n))) := by
    apply hcompact.tendsto_nhdsSet_of_mapClusterPt hmem
    intro x _ hx
    exact Submodule.subset_span hx
  have hmap : Tendsto D (𝓝ˢ (clusterSpan b : Set (Mat n))) (𝓝 0) :=
    D.continuous_of_finiteDimensional.tendsto_nhdsSet_nhds hD
  exact hmap.comp hnear

end OMA.MO474511.Bounded

#print axioms OMA.MO474511.Bounded.clusters_commute
#print axioms OMA.MO474511.Bounded.clusterSpan_abelian
#print axioms OMA.MO474511.Bounded.clusterSpan_centralizes
#print axioms OMA.MO474511.Bounded.tendsto_zero_of_vanish
