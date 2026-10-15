import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.TupleBound87

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set

namespace SevenEighths.PerturbedCanonicalFirst87

open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve
open SevenEighths.ProbeHighRowFamily

local notation "O" => HeckeFamily.O

def FirstSelectedTupleInput87 : Prop :=
  ∀(K : ℕ) (delta a b r B : ℝ),
    0 < delta → 0 < a → 0 < b → (17 / 50 : ℝ) ≤ r → 0 ≤ B →
    ∃C : ℝ, 0 < C ∧
    ∀(eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S),
      FirstTail eps S → ∀(eta : Character) (u : FreeRow)
      (T : Fin K → Finset PrimeIdeal)
      (hT : ∀i P, P ∈ T i → Supported P.val ∧ (4 : ℝ) ≤ P.val.absNorm)
      (Y : Fin K → ℝ), (∀i, 1 ≤ Y i) →
      ∀(W : Fin K → ℝ → ℂ),
      (∀i, Function.support (W i) ⊆ Icc a b) →
      (∀i y, ‖W i y‖ ≤ B) →
      ∀(x w z : ℂ), (87 / 100 : ℝ) ≤ x.re →
      (1 / 2 : ℝ) ≤ w.re → z.re = r →
      1 + eps ≤ x.re + w.re →
      (∑P : (∀i, T i), ‖continuedCorrection
        (markExclusions S (Finset.univ.image (fun i => (P i).val)))
        (markedSourceExclusions S hS
          (Finset.univ.image (fun i => (P i).val))) eta u x w z *
        ∏i, W i (((P i).val.val.absNorm : ℝ) / Y i) *
          ((P i).val.val.absNorm : ℂ) ^ (z - 1) *
          continuedCompensatedLocal eta u (P i).val
            (hT i (P i).val (P i).property).1 x w z
            (star (idealCoeff eta (P i).val.val) *
              ((P i).val.val.absNorm : ℂ) ^ x)
            (((P i).val.val.absNorm : ℂ) ^ (-w))‖) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ delta *
          ∏i, (Y i) ^ r

/-- This narrower leaf has a complete candidate proof; it does not inhabit the wide-strip input. -/
theorem first_selected_tuple_input87 : FirstSelectedTupleInput87 := by
  intro K delta a b r B hdelta ha hb hr hB
  exact continued_selected_tuple_with_correction_first87 K delta a b r B
    hdelta ha hb hr hB

end SevenEighths.PerturbedCanonicalFirst87
end
end OAI
