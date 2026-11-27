/-
 Portions through selector_spec are adapted from the public TrureTuring
 HermiteSignedMode module, commit1b672a9b9ddf56469cac348e77e27f078420eb6f.
 Those known coefficient/selector results are prior mathematics and are not
 claimed as a new resolution. The triangular cutoff and full fine-block,
 spacing, signed uniqueness and growth extension below is the present work.
 Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
 Original code license is Apache2.0; its full text is preserved below.
-/

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2026 The Omega Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.


-/

namespace A381423Certificate

open OMA.S_oeis_a381423 Finset

private def fourth (j : ℕ) : ℕ := (j + 1) * (j + 2) * (j + 3) * (j + 4)
private def divisor (r : ℕ) : ℕ := 16 * (2 * r) * (2 * r - 1)
private def rises (n r : ℕ) : Prop := 4 * r ≤ n ∧ divisor r ≤ fourth (n - 4 * r)
private instance (n r : ℕ) : Decidable (rises n r) := inferInstanceAs (Decidable (_ ∧ _))
private def candidates (n : ℕ) := (range (n + 1)).filter (rises n)
private theorem zero_candidate (n : ℕ) : 0 ∈ candidates n := by
  simp [candidates, rises, divisor, fourth]
private def mode (n : ℕ) : ℕ := (candidates n).max' ⟨0, zero_candidate n⟩
private theorem mode_rises (n : ℕ) : rises n (mode n) :=
  (mem_filter.mp (max'_mem _ _)).2
private theorem le_mode {n r : ℕ} (h : rises n r) : r ≤ mode n := by
  apply le_max'
  exact mem_filter.mpr ⟨mem_range.mpr (by have := h.1; omega), h⟩

private theorem fourth_mono : Monotone fourth := by
  intro selector b h
  unfold fourth
  gcongr
private theorem divisor_mono : Monotone divisor := by
  intro selector b h
  unfold divisor
  gcongr
private theorem rises_lower {n r s : ℕ} (h : rises n r) (hs : s ≤ r) : rises n s := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (divisor_mono hs).trans (h.2.trans (fourth_mono (by omega)))
private theorem rises_next {n r : ℕ} (h : rises n r) : rises (n + 1) r :=
  ⟨by have := h.1; omega, h.2.trans (fourth_mono (by omega))⟩
private theorem rises_previous {n r : ℕ} (h : rises (n + 1) (r + 1)) : rises n r := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (divisor_mono (by omega : r ≤ r + 1)).trans
    (h.2.trans (fourth_mono (by omega)))
private theorem mode_step (n : ℕ) : mode n ≤ mode (n + 1) ∧ mode (n + 1) ≤ mode n + 1 := by
  refine ⟨le_mode (rises_next (mode_rises n)), ?_⟩
  cases h : mode (n + 1) with
  | zero => omega
  | succ r =>
    have hr := mode_rises (n + 1)
    rw [h] at hr
    have := le_mode (rises_previous hr)
    omega

private def weight (n r : ℕ) : ℚ :=
  2 ^ (n - 4 * r) / ((2 * r).factorial * (n - 4 * r).factorial)

private theorem weight_pos (n r : ℕ) : 0 < weight n r := by
  unfold weight
  positivity

private theorem adjacent (n r : ℕ) (h : 4 * (r + 1) ≤ n) :
    weight n (r + 1) * divisor (r + 1) = weight n r * fourth (n - 4 * (r + 1)) := by
  let j := n - 4 * (r + 1)
  have hj : n - 4 * r = j + 4 := by dsimp [j]; omega
  have hr : 2 * (r + 1) = 2 * r + 2 := by omega
  have hr' : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  simp only [weight, divisor, fourth, hj, hr, hr']
  change (2 : ℚ)^j / (↑((2 * r + 2).factorial) * ↑(j.factorial)) *
      ↑(16 * (2 * r + 2) * (2 * r + 1)) =
    2^(j + 4) / (↑((2 * r).factorial) * ↑((j + 4).factorial)) *
      ↑((j + 1) * (j + 2) * (j + 3) * (j + 4))
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, pow_add]
  have hrf : (↑((2 * r).factorial) : ℚ) ≠ 0 := by positivity
  have hjf : (↑(j.factorial) : ℚ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem adjacent_le (n r : ℕ) (h : 4 * (r + 1) ≤ n) :
    weight n r ≤ weight n (r + 1) ↔ rises n (r + 1) := by
  have hd : (0 : ℚ) < divisor (r + 1) := by
    unfold divisor
    have : 0 < 2 * (r + 1) - 1 := by omega
    positivity
  have hw := weight_pos n r
  have he := adjacent n r h
  constructor
  · intro hh
    refine ⟨h, ?_⟩
    have hh' := mul_le_mul_of_nonneg_right hh hd.le
    rw [he] at hh'
    exact_mod_cast (by nlinarith : (divisor (r + 1) : ℚ) ≤ fourth (n - 4 * (r + 1)))
  · intro hh
    have hh' : (divisor (r + 1) : ℚ) ≤ fourth (n - 4 * (r + 1)) := by exact_mod_cast hh.2
    have hm := mul_le_mul_of_nonneg_left hh' hw.le
    nlinarith [he]

private theorem weight_le_mode (n r : ℕ) (hr : 4 * r ≤ n) : weight n r ≤ weight n (mode n) := by
  by_cases h : r ≤ mode n
  · have aux : ∀ k, k ≤ mode n → ∀ i, i ≤ k → weight n i ≤ weight n k := by
      intro k
      induction k with
      | zero =>
        intro hk i hi
        have : i = 0 := by omega
        subst i
        rfl
      | succ k ih =>
        intro hk i hi
        by_cases hik : i ≤ k
        · exact (ih (by omega) i hik).trans
            ((adjacent_le n k (by have := (mode_rises n).1; omega)).mpr
              (rises_lower (mode_rises n) hk))
        · have : i = k + 1 := by omega
          subst i
          rfl
    exact aux _ le_rfl r h
  · have aux : ∀ k, 4 * k ≤ n → mode n ≤ k → weight n k ≤ weight n (mode n) := by
      intro k
      induction k with
      | zero =>
        intro hk hm
        have : mode n = 0 := by omega
        rw [this]
      | succ k ih =>
        intro hk hm
        by_cases hkm : mode n ≤ k
        · have hnot : ¬ rises n (k + 1) := fun hh => by have := le_mode hh; omega
          have hlt : weight n (k + 1) < weight n k :=
            lt_of_not_ge (fun hh => hnot ((adjacent_le n k hk).mp hh))
          exact hlt.le.trans (ih (by omega) hkm)
        · have : mode n = k + 1 := by omega
          rw [this]
    exact aux r hr (by omega)

private theorem weight_lt_mode (n r : ℕ) (hr : 4 * r ≤ n) (hm : mode n < r) :
    weight n r < weight n (mode n) := by
  cases r with
  | zero => omega
  | succ r =>
    have hnot : ¬ rises n (r + 1) := fun hh => by have := le_mode hh; omega
    have hlt : weight n (r + 1) < weight n r :=
      lt_of_not_ge (fun hh => hnot ((adjacent_le n r hr).mp hh))
    exact hlt.trans_le (weight_le_mode n r (by omega))

private theorem positive_coefficient (n r : ℕ) (hr : 4 * r ≤ n) :
    signedCoeff n (n - 4 * r) = n.factorial * weight n r := by
  have hs : n - (n - 4 * r) = 4 * r := by omega
  have he : 4 * r/2 = 2 * r := by omega
  simp [signedCoeff, hs, he, show (4 * r)%2 = 0 by omega, show (n - 4 * r ≤ n) by omega, weight,
    show (-1 : ℚ)^(2 * r) = 1 by rw [pow_mul]; norm_num]
  <;> ring

private theorem coefficient_cases (n j : ℕ) : signedCoeff n j ≤ 0 ∨
    ∃ r, 4 * r ≤ n ∧ j = n - 4 * r ∧ signedCoeff n j = n.factorial * weight n r := by
  by_cases h : j ≤ n ∧ (n - j)%2 = 0
  · by_cases h4 : (n - j)%4 = 0
    · right
      let r := (n - j)/4
      have hr : n - j = 4 * r := by dsimp [r]; omega
      have hj : j = n - 4 * r := by omega
      exact ⟨r, by omega, hj, hj ▸ positive_coefficient n r (by omega)⟩
    · left
      have he : (n - j)/2 = 2 * ((n - j)/4) + 1 := by omega
      have hp : (-1 : ℚ)^((n - j)/2) = -1 := by
        rw [he, pow_add, pow_mul]
        norm_num
      rw [signedCoeff, if_pos h, hp]
      have : (0 : ℚ) < n.factorial := by positivity
      have : (0 : ℚ) < 2^j := by positivity
      have : (0 : ℚ) < ((n - j)/2).factorial * j.factorial := by positivity
      exact (div_neg_of_neg_of_pos (by nlinarith) this).le
  · left
    simp [signedCoeff, h]

/-- The smallest exponent maximizing the signed coefficient. -/
noncomputable def selector (n : ℕ) : ℕ := n - 4 * mode n

theorem polynomial_coeff (n j : ℕ) (hj : j ≤ n) :
    (physicistsHermite n).coeff j = signedCoeff n j := by
  classical
  simp only [physicistsHermite, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases h : j ≤ n ∧ (n - j)%2 = 0
  · rw [signedCoeff, if_pos h]
    have he : n - 2 * ((n - j)/2) = j := by omega
    rw [sum_eq_single ((n - j)/2)]
    · simp [he]
    · intro b hb hne
      have hn : 2 * b ≤ n := by have := mem_range.mp hb; omega
      have hh : n - 2 * b ≠ j := by omega
      simp [hh, Ne.symm hh]
    · intro hh
      exact (hh (mem_range.mpr (by omega))).elim
  · rw [signedCoeff, if_neg h]
    apply sum_eq_zero
    intro b hb
    have hn : 2 * b ≤ n := by have := mem_range.mp hb; omega
    have hh : n - 2 * b ≠ j := by
      intro he
      apply h
      constructor <;> omega
    simp [hh, Ne.symm hh]

private theorem selector_spec (n : ℕ) : IsSmallestMax n (selector n) := by
  have hm := (mode_rises n).1
  have ha : selector n ≤ n := Nat.sub_le _ _
  have hcoeff := positive_coefficient n (mode n) hm
  have hp : (0 : ℚ) < n.factorial * weight n (mode n) := by
    have := weight_pos n (mode n)
    positivity
  refine ⟨ha, ?_, ?_⟩
  · intro k hk
    rw [polynomial_coeff n k hk, polynomial_coeff n (selector n) ha]
    change signedCoeff n k ≤ signedCoeff n (n - 4 * mode n)
    rw [hcoeff]
    rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
    · exact h.trans hp.le
    · rw [hc]
      exact mul_le_mul_of_nonneg_left (weight_le_mode n r hr) (by positivity)
  · intro k hk he
    rw [polynomial_coeff n k hk, polynomial_coeff n (selector n) ha] at he
    change signedCoeff n k = signedCoeff n (n - 4 * mode n) at he
    rw [hcoeff] at he
    rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
    · linarith
    · have hle : r ≤ mode n := by
        by_contra hh
        have ht := weight_lt_mode n r hr (by omega)
        have hnf : (0 : ℚ) < n.factorial := by positivity
        rw [hc] at he
        nlinarith
      dsimp [selector]
      omega

