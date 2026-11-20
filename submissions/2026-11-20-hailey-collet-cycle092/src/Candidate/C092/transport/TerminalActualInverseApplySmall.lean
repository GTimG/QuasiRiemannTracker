/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal original short column at every positive subunit scale.
Finite ideal counting pays the square-root normalization without replacing X. -/
import Candidate.C092.transport.TerminalProfileUniformSup
import Candidate.C092.transport.StrongPairRegularTerminalZero
import Candidate.C092.transport.MediumReplaceSourceUpper

set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualInverseApply
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open ConcretePrimeRowBridge CanonicalRowCompletion CenteredMomentPrimeSlot
open HeckePrimeAnnular HeckeDyadic CenteredMomentHeckeSlots CenteredMomentCoreFloor
open CenteredMomentHeckeHeight CenteredMomentHeckeExpansion CenteredMomentSourceMass
open CenteredMomentWholeSlotDeletion Qrh.JointDetector WholeWordAmplification
open QRH.Cycle092.OrdinaryColumn
local notation "O" => HeckeFamily.O

theorem short_original_subunit (η : Character) (mask A z : O) (W : ℝ→ℂ)
    (t X B : ℝ) (hX : 0 < X) (hX1 : X ≤ 1) (hB : 0 ≤ B)
    (hs : Function.support W ⊆ Iic (9/4:ℝ)) (hW : ∀ x,‖W x‖ ≤ B) :
    ‖original η mask A z W t X‖ ≤ 288*B := by
  rw [as_slot η mask A z W t (9/4) X hs hX]
  change ‖(Real.sqrt X:ℂ)⁻¹*rowSlot η mask A z (idealBall ((9/4)*X)) (fun I=>W ((I.absNorm:ℝ)/X)) t‖ ≤ _
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X)]
  have hr := rowSlot_bound η mask A z (idealBall ((9/4)*X))
    (fun I=>W ((I.absNorm:ℝ)/X)) t ((9/4)*X) B (by positivity) hB
    (fun I _=>hW _) (fun I hI _=>(mem_idealBall _ _).mp hI |>.2)
  have hroot : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have heq : (Real.sqrt X)⁻¹*(128*((9/4)*X)*B)=(288*B)*Real.sqrt X := by
    field_simp
    rw [Real.sq_sqrt hX.le]
    ring
  calc
    _ ≤ (Real.sqrt X)⁻¹*(128*((9/4)*X)*B) := mul_le_mul_of_nonneg_left (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hr) (by positivity)
    _ = (288*B)*Real.sqrt X := heq
    _ ≤ 288*B := by
      have h := mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hX1) (show 0 ≤ 288*B by positivity)
      simpa only [mul_one] using h

theorem twist_profile_support {W : ℝ→ℂ} {A B σ freq : ℝ}
    (hs : Function.support W ⊆ Icc A B) :
    Function.support (twistProfile W σ freq) ⊆ Iic B := by
  intro x hx
  have hx' : W x≠0 := by
    intro h
    exact hx (by simp [twistProfile,HeckeDyadic.shift,h])
  exact (hs hx').2

#print axioms short_original_subunit
#print axioms twist_profile_support
end
end QRH.Cycle092.TerminalActualInverseApply
