import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineAmplification
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open CenteredMomentEnergyFirstAnnularAdmission

variable [Cycle63.AffineLedger] in
/-- The bound of the amplifier coefficient `(amplifierCap 2 0 1 + 6 a) / (a / 2)` over the cells of the slot window: the
coefficient is `15 / a + 12` and the amplifier width `a` of a cell is at least the floor. -/
def geometryAmplifierCoefficientCap : ℝ := 15/Cycle63.AffineLedger.amplifierFloor+12

variable [Cycle63.AffineLedger] in
theorem geometryAmplifierCoefficientCap_pos : 0<geometryAmplifierCoefficientCap := by
  have hfloor:=Cycle63.AffineLedger.amplifierFloor_pos
  unfold geometryAmplifierCoefficientCap
  positivity

variable [Cycle63.AffineLedger] in
/-- One numerical coefficient works for every original-width cell. -/
theorem geometry_affine_main_amplifier_bound (beta : ℝ)
    (hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop) :
    let a:=Cycle63.AffineLedger.amp beta
    0≤(amplifierCap 2 0 1+6*a)/(a/2) ∧
      (amplifierCap 2 0 1+6*a)/(a/2)≤geometryAmplifierCoefficientCap := by
  intro a
  have ha:=Cycle63.AffineLedger.amp_pos hb
  have hlo:=(Cycle63.AffineLedger.amp_bounds hb).1
  change 0<a at ha
  change Cycle63.AffineLedger.amplifierFloor≤a at hlo
  have hfloor:=Cycle63.AffineLedger.amplifierFloor_pos
  constructor
  · unfold amplifierCap
    positivity
  · have hcap : amplifierCap 2 0 1=15/2 := by
      norm_num only [amplifierCap,max_eq_left (by norm_num : (0:ℝ)≤2)]
    have hcoefficient : (amplifierCap 2 0 1+6*a)/(a/2)=15/a+12 := by
      rw [hcap]
      field_simp
      ring
    rw [hcoefficient]
    unfold geometryAmplifierCoefficientCap
    have hdiv : 15/a≤15/Cycle63.AffineLedger.amplifierFloor :=
      div_le_div_of_nonneg_left (by norm_num) hfloor hlo
    linarith

/-- Both orientations use the same E and reciprocal physical compensator.
The asymmetric fixed support constant is absorbed into E. -/
theorem geometry_physical_side_join (reflected : Bool) (C K control budget : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (hK : 0≤K) (hc : 0≤ control)
    (hb : budget≤K*geometryHighFactor reflected C key*control) :
    let E:=K*(1+2*C^2)*control
    budget ≤ (if reflected then E/geometryDCompensator key
      else E*geometryDCompensator key) := by
  intro E
  have hh:=(geometryDCompensator_pos key).le
  cases reflected
  · simp only [geometryHighFactor,Bool.false_eq_true,ite_false] at hb ⊢
    dsimp only [E]
    nlinarith [mul_nonneg (mul_nonneg hK hc) hh]
  · simp only [geometryHighFactor,ite_true] at hb ⊢
    dsimp only [E]
    rw [div_eq_mul_inv]
    have hnonneg : 0≤K*C^2*control*(geometryDCompensator key)⁻¹ := by positivity
    nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
