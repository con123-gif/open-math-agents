import Mathlib

/-!
# Semisimplicity questions for joint centralizers with transpose

Source: https://mathoverflow.net/questions/487192
Original question: Mare (MathOverflow user61949), February 4, 2025, CC BY-SA 4.0.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).

The three conjuncts retain all three explicit semisimplicity questions in the
source. The first concerns an arbitrary finite poset, the second the product
of n chains with t elements (the source's t=2 gives the Boolean lattice), and
the third arbitrary invertible matrices over characteristic-zero fields.
All centralizers are associative, unital algebras and transpose is ordinary
transpose. Decidability instances merely allow the finite incidence matrices
to be written; every finite poset admits these instances classically.
The open-ended requests for an interpretation, dimensions, and Wedderburn
decompositions assert no formula that could be included as another conjecture.
Steinberg's source comments already address the positive real/poset cases.
Our disproof addresses the third conjunct; it does not refute the first two.
-/

namespace OMA.S_mo_487192

def jointCentralizer (K : Type) [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : Subalgebra K (Matrix (Fin n) (Fin n) K) :=
  Subalgebra.centralizer K ({A, A.transpose} : Set (Matrix (Fin n) (Fin n) K))

def cartan (K : Type) [Field K] (P : Type) [PartialOrder P] [DecidableLE P] :
    Matrix P P K :=
  fun i j => if i ≤ j then 1 else 0

def posetCentralizer (K : Type) [Field K] (P : Type) [PartialOrder P]
    [Fintype P] [DecidableEq P] [DecidableLE P] : Subalgebra K (Matrix P P K) :=
  Subalgebra.centralizer K ({cartan K P, (cartan K P).transpose} : Set (Matrix P P K))

open scoped Classical in
theorem main :
    (∀ (K : Type) [Field K] [CharZero K] (P : Type) [PartialOrder P]
      [Fintype P] [DecidableEq P] [DecidableLE P],
      IsSemisimpleRing (posetCentralizer K P)) ∧
    (∀ (K : Type) [Field K] [CharZero K] (n t : ℕ),
      0 < n → 0 < t → IsSemisimpleRing (posetCentralizer K (Fin n → Fin t))) ∧
    (∀ (K : Type) [Field K] [CharZero K] (n : ℕ),
      0 < n → ∀ A : Matrix (Fin n) (Fin n) K,
        IsUnit A → IsSemisimpleRing (jointCentralizer K A)) := by
  sorry

end OMA.S_mo_487192



noncomputable section

-- Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-- GPT-6; exact serving variant not exposed.
-- Question 3 only: a symmetric, invertible 3-by-3 complex counterexample.

namespace MO487192Certificate

lemma central_square_zero_eq_zero {R : Type*} [Ring R] [IsSemisimpleRing R]
    (x : R) (hcentral : ∀ r : R, x * r = r * x) (hsq : x * x = 0) : x = 0 := by
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (Ideal.span ({x} : Set R))
  have hemem : e ∈ Ideal.span ({x} : Set R) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self e
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hemem
  have hesq : e * e = 0 := by
    rw [← ht, ← pow_two, (show Commute t x from (hcentral t).symm).mul_pow, pow_two x, hsq, mul_zero]
  have hezero : e = 0 := (show e * e = e from he).symm.trans hesq
  have hxmem : x ∈ Ideal.span ({x} : Set R) := Ideal.mem_span_singleton_self x
  rw [hI, hezero] at hxmem
  simpa using hxmem

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def N : Mat := !![Complex.I, 1, 0; 1, -Complex.I, 0; 0, 0, 0]

def A : Mat := 1 + N

lemma N_square : N * N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_succ]

lemma N_transpose : N.transpose = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma A_transpose : A.transpose = A := by
  simp [A, N_transpose]

lemma A_isUnit : IsUnit A :=
  IsNilpotent.isUnit_one_add ⟨2, by simpa only [pow_two] using N_square⟩

abbrev R := OMA.S_mo_487192.jointCentralizer ℂ A

noncomputable def nilpotentElement : R := ⟨N, by
  apply (Subalgebra.mem_centralizer_iff ℂ).mpr
  intro g hg
  have hgA : g = A := by simpa [A_transpose] using hg
  subst g
  dsimp [A]
  noncomm_ring⟩

lemma nilpotentElement_square : nilpotentElement * nilpotentElement = 0 := Subtype.ext N_square

lemma nilpotentElement_nonzero : nilpotentElement ≠ 0 := by
  intro h
  have hN : N = 0 := congrArg (fun x : R => (x : Mat)) h
  have h01 := congrArg (fun M : Mat => M 0 1) hN
  norm_num [N] at h01

lemma nilpotentElement_central (x : R) :
    nilpotentElement * x = x * nilpotentElement := by
  apply Subtype.ext
  have hx := (Subalgebra.mem_centralizer_iff ℂ).mp x.property A (by simp)
  change A * (x : Mat) = (x : Mat) * A at hx
  change N * (x : Mat) = (x : Mat) * N
  simpa only [A, add_mul, mul_add, one_mul, mul_one, add_left_cancel_iff] using hx

end MO487192Certificate

open MO487192Certificate

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_487192.main) := by
  intro h
  letI : IsSemisimpleRing R := h.2.2 ℂ 3 (by decide) A A_isUnit
  exact nilpotentElement_nonzero (central_square_zero_eq_zero nilpotentElement
    nilpotentElement_central nilpotentElement_square)


#print axioms OMA.disproof
