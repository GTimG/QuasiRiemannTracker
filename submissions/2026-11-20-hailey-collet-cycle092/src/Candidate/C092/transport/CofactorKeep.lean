/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Removing the sixth-power cofactor preserves the original exceptional-row split. -/
import Candidate.C092.transport.CofactorPairBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRowMask

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

theorem fixedInducingRow_on_root (η : Character) (Q : Ideal O) (m A : O)
    (hm : m ≠ 0) (hA : A ≠ 0) (hLam : goodLambda ∣ m) (h2 : (2:O) ∣ m)
    (u : FreeRow) (B : NonzeroIdeal) :
    FixedInducingRow η Q m A (rowMap (u,B)) ↔ FixedInducingRow η Q m A u.val := by
  let g := idealGenerator B.val
  have hg : g ≠ 0 := idealGenerator_ne_zero _ B.property
  have he : rowTwist (elementHom η) m 1 (A * rowMap (u,B)) =
      rowTwist (elementHom η) (m*g) 1 (A*u.val) := by
    unfold rowTwist
    rw [show m^6 * (1:O)^4 * (A * rowMap (u,B)) = (m*g)^6 * (1:O)^4 * (A*u.val) by
      unfold rowMap; dsimp [g]; ring]
  rw [← CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η Q m g A u.val hm hg hA u.property.1 hLam h2]
  unfold FixedInducingRow
  rw [he]

theorem initialKeep_on_root (η : Character) (Q : Ideal O) (u : FreeRow) (B : NonzeroIdeal) :
    initialKeep η Q (rowMap (u,B)) ↔ initialKeep η Q u.val := by
  have hm := mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero (1 : Ideal O) one_ne_zero)
  have hLam : goodLambda ∣ fixedBadMask := dvd_mul_right _ _
  have h2 : (2:O) ∣ fixedBadMask := dvd_mul_left _ _
  unfold initialKeep
  rw [fixedInducingRow_on_root η Q _ 1 hm one_ne_zero
    (hLam.trans (dvd_mul_right _ _)) (h2.trans (dvd_mul_right _ _)) u B]
  exact ⟨fun h => ⟨u.property.1,h.2⟩, fun h => ⟨rowMap_ne_zero _,h.2⟩⟩

#print axioms initialKeep_on_root
end
end QRH.Cycle092.CofactorOrdinary
