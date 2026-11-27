import Mathlib

-- MO235344 (Jiro, 2016), pending statement PR3755 by byrohan.
-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6.2).
-- Repair of previous failed probes. Exact real statement; no rational cast or kernel permutation evaluation.
noncomputable section
open scoped Matrix BigOperators
namespace MatrixLane235344Repair
def IrreducibleSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ →
    ∃ i ∈ s, ∃ j ∉ s, M i j ≠ 0
noncomputable def principalMinor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) : ℝ :=
  (M.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).det
def A : Matrix (Fin 5) (Fin 5) ℝ := !![(1/3),(2/3),(-2/3),(-2/3),0;(-4/3),(1/3),(2/3),(2/3),0;(2/3),(-2/3),(-1/3),(-4/3),0;0,0,0,0,1;(-2/3),(2/3),(-2/3),(1/3),0]
def C : Matrix (Fin 5) (Fin 5) ℝ := !![(1/3),(-2/3),(-2/3),0,(-2/3);(4/3),(1/3),(-2/3),0,(-2/3);(2/3),(2/3),(-1/3),0,(-4/3);(-2/3),(-2/3),(-2/3),0,(1/3);0,0,0,1,0]
set_option maxRecDepth 10000
set_option maxHeartbeats 0
lemma minorWith (M : Matrix (Fin 5) (Fin 5) ℝ) (s : Finset (Fin 5))
    {k : ℕ} (h : s.card = k) (f : Fin k → Fin 5)
    (hf : ∀ i, f i ∈ s) (hm : StrictMono f) :
    principalMinor M s = (M.submatrix f f).det := by
  subst k
  unfold principalMinor
  rw [← Finset.orderEmbOfFin_unique rfl hf hm]

lemma minor_0 : principalMinor A (∅ : Finset (Fin 5)) = principalMinor C (∅ : Finset (Fin 5)) := by
  let f : Fin 0 → Fin 5 := ![]
  have hc : (∅ : Finset (Fin 5)).card = 0 := by decide
  have hf : ∀ i, f i ∈ (∅ : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_1 : principalMinor A ({0} : Finset (Fin 5)) = principalMinor C ({0} : Finset (Fin 5)) := by
  let f : Fin 1 → Fin 5 := ![0]
  have hc : ({0} : Finset (Fin 5)).card = 1 := by decide
  have hf : ∀ i, f i ∈ ({0} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_2 : principalMinor A ({1} : Finset (Fin 5)) = principalMinor C ({1} : Finset (Fin 5)) := by
  let f : Fin 1 → Fin 5 := ![1]
  have hc : ({1} : Finset (Fin 5)).card = 1 := by decide
  have hf : ∀ i, f i ∈ ({1} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_3 : principalMinor A ({0,1} : Finset (Fin 5)) = principalMinor C ({0,1} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![0,1]
  have hc : ({0,1} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({0,1} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_4 : principalMinor A ({2} : Finset (Fin 5)) = principalMinor C ({2} : Finset (Fin 5)) := by
  let f : Fin 1 → Fin 5 := ![2]
  have hc : ({2} : Finset (Fin 5)).card = 1 := by decide
  have hf : ∀ i, f i ∈ ({2} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_5 : principalMinor A ({0,2} : Finset (Fin 5)) = principalMinor C ({0,2} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![0,2]
  have hc : ({0,2} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({0,2} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_6 : principalMinor A ({1,2} : Finset (Fin 5)) = principalMinor C ({1,2} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![1,2]
  have hc : ({1,2} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({1,2} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_7 : principalMinor A ({0,1,2} : Finset (Fin 5)) = principalMinor C ({0,1,2} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![0,1,2]
  have hc : ({0,1,2} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({0,1,2} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_8 : principalMinor A ({3} : Finset (Fin 5)) = principalMinor C ({3} : Finset (Fin 5)) := by
  let f : Fin 1 → Fin 5 := ![3]
  have hc : ({3} : Finset (Fin 5)).card = 1 := by decide
  have hf : ∀ i, f i ∈ ({3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_9 : principalMinor A ({0,3} : Finset (Fin 5)) = principalMinor C ({0,3} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![0,3]
  have hc : ({0,3} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({0,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_10 : principalMinor A ({1,3} : Finset (Fin 5)) = principalMinor C ({1,3} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![1,3]
  have hc : ({1,3} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({1,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_11 : principalMinor A ({0,1,3} : Finset (Fin 5)) = principalMinor C ({0,1,3} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![0,1,3]
  have hc : ({0,1,3} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({0,1,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_12 : principalMinor A ({2,3} : Finset (Fin 5)) = principalMinor C ({2,3} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![2,3]
  have hc : ({2,3} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({2,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_13 : principalMinor A ({0,2,3} : Finset (Fin 5)) = principalMinor C ({0,2,3} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![0,2,3]
  have hc : ({0,2,3} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({0,2,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_14 : principalMinor A ({1,2,3} : Finset (Fin 5)) = principalMinor C ({1,2,3} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![1,2,3]
  have hc : ({1,2,3} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({1,2,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_15 : principalMinor A ({0,1,2,3} : Finset (Fin 5)) = principalMinor C ({0,1,2,3} : Finset (Fin 5)) := by
  let f : Fin 4 → Fin 5 := ![0,1,2,3]
  have hc : ({0,1,2,3} : Finset (Fin 5)).card = 4 := by decide
  have hf : ∀ i, f i ∈ ({0,1,2,3} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_16 : principalMinor A ({4} : Finset (Fin 5)) = principalMinor C ({4} : Finset (Fin 5)) := by
  let f : Fin 1 → Fin 5 := ![4]
  have hc : ({4} : Finset (Fin 5)).card = 1 := by decide
  have hf : ∀ i, f i ∈ ({4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_17 : principalMinor A ({0,4} : Finset (Fin 5)) = principalMinor C ({0,4} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![0,4]
  have hc : ({0,4} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({0,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_18 : principalMinor A ({1,4} : Finset (Fin 5)) = principalMinor C ({1,4} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![1,4]
  have hc : ({1,4} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({1,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_19 : principalMinor A ({0,1,4} : Finset (Fin 5)) = principalMinor C ({0,1,4} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![0,1,4]
  have hc : ({0,1,4} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({0,1,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_20 : principalMinor A ({2,4} : Finset (Fin 5)) = principalMinor C ({2,4} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![2,4]
  have hc : ({2,4} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({2,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_21 : principalMinor A ({0,2,4} : Finset (Fin 5)) = principalMinor C ({0,2,4} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![0,2,4]
  have hc : ({0,2,4} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({0,2,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_22 : principalMinor A ({1,2,4} : Finset (Fin 5)) = principalMinor C ({1,2,4} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![1,2,4]
  have hc : ({1,2,4} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({1,2,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_23 : principalMinor A ({0,1,2,4} : Finset (Fin 5)) = principalMinor C ({0,1,2,4} : Finset (Fin 5)) := by
  let f : Fin 4 → Fin 5 := ![0,1,2,4]
  have hc : ({0,1,2,4} : Finset (Fin 5)).card = 4 := by decide
  have hf : ∀ i, f i ∈ ({0,1,2,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_24 : principalMinor A ({3,4} : Finset (Fin 5)) = principalMinor C ({3,4} : Finset (Fin 5)) := by
  let f : Fin 2 → Fin 5 := ![3,4]
  have hc : ({3,4} : Finset (Fin 5)).card = 2 := by decide
  have hf : ∀ i, f i ∈ ({3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_25 : principalMinor A ({0,3,4} : Finset (Fin 5)) = principalMinor C ({0,3,4} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![0,3,4]
  have hc : ({0,3,4} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({0,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_26 : principalMinor A ({1,3,4} : Finset (Fin 5)) = principalMinor C ({1,3,4} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![1,3,4]
  have hc : ({1,3,4} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({1,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_27 : principalMinor A ({0,1,3,4} : Finset (Fin 5)) = principalMinor C ({0,1,3,4} : Finset (Fin 5)) := by
  let f : Fin 4 → Fin 5 := ![0,1,3,4]
  have hc : ({0,1,3,4} : Finset (Fin 5)).card = 4 := by decide
  have hf : ∀ i, f i ∈ ({0,1,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_28 : principalMinor A ({2,3,4} : Finset (Fin 5)) = principalMinor C ({2,3,4} : Finset (Fin 5)) := by
  let f : Fin 3 → Fin 5 := ![2,3,4]
  have hc : ({2,3,4} : Finset (Fin 5)).card = 3 := by decide
  have hf : ∀ i, f i ∈ ({2,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_29 : principalMinor A ({0,2,3,4} : Finset (Fin 5)) = principalMinor C ({0,2,3,4} : Finset (Fin 5)) := by
  let f : Fin 4 → Fin 5 := ![0,2,3,4]
  have hc : ({0,2,3,4} : Finset (Fin 5)).card = 4 := by decide
  have hf : ∀ i, f i ∈ ({0,2,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_30 : principalMinor A ({1,2,3,4} : Finset (Fin 5)) = principalMinor C ({1,2,3,4} : Finset (Fin 5)) := by
  let f : Fin 4 → Fin 5 := ![1,2,3,4]
  have hc : ({1,2,3,4} : Finset (Fin 5)).card = 4 := by decide
  have hf : ∀ i, f i ∈ ({1,2,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minor_31 : principalMinor A ({0,1,2,3,4} : Finset (Fin 5)) = principalMinor C ({0,1,2,3,4} : Finset (Fin 5)) := by
  let f : Fin 5 → Fin 5 := ![0,1,2,3,4]
  have hc : ({0,1,2,3,4} : Finset (Fin 5)).card = 5 := by decide
  have hf : ∀ i, f i ∈ ({0,1,2,3,4} : Finset (Fin 5)) := by
    intro i
    fin_cases i <;> decide
  have hm : StrictMono f := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  rw [minorWith A _ hc f hf hm, minorWith C _ hc f hf hm]
  simp only [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  norm_num [A, C, f, Matrix.vecCons, Fin.cons, Fin.succAbove]

lemma minors (s : Finset (Fin 5)) : principalMinor A s = principalMinor C s := by
  have hs : s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {0,1} ∨ s = {2} ∨ s = {0,2} ∨ s = {1,2} ∨ s = {0,1,2} ∨ s = {3} ∨ s = {0,3} ∨ s = {1,3} ∨ s = {0,1,3} ∨ s = {2,3} ∨ s = {0,2,3} ∨ s = {1,2,3} ∨ s = {0,1,2,3} ∨ s = {4} ∨ s = {0,4} ∨ s = {1,4} ∨ s = {0,1,4} ∨ s = {2,4} ∨ s = {0,2,4} ∨ s = {1,2,4} ∨ s = {0,1,2,4} ∨ s = {3,4} ∨ s = {0,3,4} ∨ s = {1,3,4} ∨ s = {0,1,3,4} ∨ s = {2,3,4} ∨ s = {0,2,3,4} ∨ s = {1,2,3,4} ∨ s = {0,1,2,3,4} := by
    fin_cases s <;> decide
  rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · rw [h0]; exact minor_0
  · rw [h1]; exact minor_1
  · rw [h2]; exact minor_2
  · rw [h3]; exact minor_3
  · rw [h4]; exact minor_4
  · rw [h5]; exact minor_5
  · rw [h6]; exact minor_6
  · rw [h7]; exact minor_7
  · rw [h8]; exact minor_8
  · rw [h9]; exact minor_9
  · rw [h10]; exact minor_10
  · rw [h11]; exact minor_11
  · rw [h12]; exact minor_12
  · rw [h13]; exact minor_13
  · rw [h14]; exact minor_14
  · rw [h15]; exact minor_15
  · rw [h16]; exact minor_16
  · rw [h17]; exact minor_17
  · rw [h18]; exact minor_18
  · rw [h19]; exact minor_19
  · rw [h20]; exact minor_20
  · rw [h21]; exact minor_21
  · rw [h22]; exact minor_22
  · rw [h23]; exact minor_23
  · rw [h24]; exact minor_24
  · rw [h25]; exact minor_25
  · rw [h26]; exact minor_26
  · rw [h27]; exact minor_27
  · rw [h28]; exact minor_28
  · rw [h29]; exact minor_29
  · rw [h30]; exact minor_30
  · rw [h31]; exact minor_31
lemma ac : A * C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,C,Matrix.vecCons,Fin.cons,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
lemma support : IrreducibleSupport A := by
  classical
  intro s hs hp
  by_contra h
  have closed : ∀ i ∈ s, ∀ j, A i j ≠ 0 → j ∈ s := by
    intro i hi j hij
    by_contra hj
    exact h ⟨i,hi,j,hj,hij⟩
  obtain ⟨i,hi⟩ := hs
  have h0 : (0 : Fin 5) ∈ s := by
    fin_cases i
    · exact hi
    · exact closed 1 hi 0 (by norm_num [A,Matrix.vecCons,Fin.cons])
    · exact closed 2 hi 0 (by norm_num [A,Matrix.vecCons,Fin.cons])
    · exact closed 4 (closed 3 hi 4 (by norm_num [A,Matrix.vecCons,Fin.cons])) 0 (by norm_num [A,Matrix.vecCons,Fin.cons])
    · exact closed 4 hi 0 (by norm_num [A,Matrix.vecCons,Fin.cons])
  have h1 := closed 0 h0 1 (by norm_num [A,Matrix.vecCons,Fin.cons])
  have h2 := closed 0 h0 2 (by norm_num [A,Matrix.vecCons,Fin.cons])
  have h3 := closed 0 h0 3 (by norm_num [A,Matrix.vecCons,Fin.cons])
  have h4 := closed 3 h3 4 (by norm_num [A,Matrix.vecCons,Fin.cons])
  apply hp
  apply Finset.eq_univ_of_forall
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
lemma no_diag (d : Fin 5 → ℝ) (hd : ∀ i, d i ≠ 0) :
    ¬ (A * Matrix.diagonal d = Matrix.diagonal d * C ∨
       A.transpose * Matrix.diagonal d = Matrix.diagonal d * C) := by
  rintro (h|h)
  · have e := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 0 4) h
    norm_num [Matrix.mul_diagonal,Matrix.diagonal_mul,A,C,Matrix.vecCons,Fin.cons] at e
    exact hd 0 (by linarith)
  · have e1 := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 0 1) h
    have e2 := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 1 2) h
    have e3 := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 2 0) h
    norm_num [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.transpose_apply,A,C,Matrix.vecCons,Fin.cons] at e1 e2 e3
    exact hd 0 (by linarith)
end MatrixLane235344Repair
open MatrixLane235344Repair
theorem OMA.disproof : ¬ (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), IsUnit M.det →
      IrreducibleSupport M →
      (∀ s : Finset (Fin n), principalMinor M s = principalMinor M⁻¹ s) →
      ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧
        (M * Matrix.diagonal d = Matrix.diagonal d * M⁻¹ ∨
         M.transpose * Matrix.diagonal d = Matrix.diagonal d * M⁻¹)) := by
  intro h
  have hinv : A⁻¹ = C := Matrix.inv_eq_right_inv ac
  have hunit : IsUnit A.det := Matrix.isUnit_det_of_right_inverse ac
  obtain ⟨d,hd,he⟩ := h 5 A hunit support (by simpa only [hinv] using minors)
  exact no_diag d hd (by simpa only [hinv] using he)
#print axioms minors
#print axioms OMA.disproof
