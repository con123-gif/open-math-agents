import Mathlib

/-!
The four-by-four alternating determinant over F2. The scalar identity is
kernel-decided over all64 possible six-entry matrices, so it is a complete
finite algebra lemma. It does not replace the missing arbitrary-order graph
argument. Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped Matrix

def alternatingFour (a b c d e f : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, a, b, c; a, 0, d, e; b, d, 0, f; c, e, f, 0]

set_option maxRecDepth 10000 in
lemma det_alternatingFour (a b c d e f : ZMod 2) :
    (alternatingFour a b c d e f).det = a * f + b * e + c * d := by
  have h : ∀ a b c d e f : ZMod 2,
      (alternatingFour a b c d e f).det = a * f + b * e + c * d := by decide
  exact h a b c d e f

lemma det_four_submatrix_mod_two {I : Type*} (A : Matrix I I (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (i j k l : I) :
    (A.submatrix ![i, j, k, l] ![i, j, k, l]).det =
      A i j * A k l + A i k * A j l + A i l * A j k := by
  have hm : A.submatrix ![i, j, k, l] ![i, j, k, l] =
      alternatingFour (A i j) (A i k) (A i l) (A j k) (A j l) (A k l) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [alternatingFour, Matrix.submatrix_apply, hd,
        hA.apply i j, hA.apply i k, hA.apply i l,
        hA.apply j k, hA.apply j l, hA.apply k l]
  rw [hm, det_alternatingFour]

end OMA.MO513259

#print axioms OMA.MO513259.det_four_submatrix_mod_two
