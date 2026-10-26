/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalRoundedPosition

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Cycle153
noncomputable section
open Cycle63.Optimization

/-- The actual regional deletion remains literal. Its upward rounding
displacement is an explicit finite source fee, separate from the further
whole-slot deletion mesh. -/
theorem rounded_deletion_bounds (S : RegionalStage) {g B n1 n2 z : ℝ}
    (hg : 0<g) (hK : amplifierRatio S.price S.intercept S.q ≤ 7)
    (hI0 : 0 ≤ S.intercept) (hI1 : S.intercept ≤ 1) :
    let P := roundedPosition g B n1 n2 z
    let gap := planeGap S.price S.intercept S.lam B z
    let gapActual := planeGap S.price S.intercept S.lam P.B P.slotTop
    let a := planeAmplifier S.price S.intercept S.q S.lam B z
    let del := (gap+6*S.intercept*a)/(6*S.price)
    let delActual := (gapActual+6*S.intercept*S.amp P)/(6*S.price)
    del ≤ delActual ∧ delActual ≤ del+2200*g := by
  intro P gap gapActual a del delActual
  have hB := roundUp_bounds hg B
  have hz := roundUp_bounds hg z
  have ha := rounded_amplifier_bounds S (B:=B) (z:=z) (n₁:=n1) (n₂:=n2) hg hK
  change a ≤ S.amp P ∧ S.amp P ≤ a+42*g at ha
  have hc0 : 0 ≤ 6*S.price-S.lam := by linarith only [S.lam_le_six_price]
  have hc5 : 6*S.price-S.lam ≤ 5 := by linarith only [S.price_le_one,S.one_le_lam]
  have hgap : gap ≤ gapActual ∧ gapActual ≤ gap+6*g := by
    have hzlo := mul_le_mul_of_nonneg_left hz.1 hc0
    have hzhi := mul_le_mul_of_nonneg_left hz.2 hc0
    have hcg := mul_le_mul_of_nonneg_right hc5 hg.le
    dsimp only [gap,gapActual,planeGap,P,roundedPosition]
    constructor <;> nlinarith only [hB,hzlo,hzhi,hcg]
  have hnumlo : gap+6*S.intercept*a ≤ gapActual+6*S.intercept*S.amp P := by
    have hm := mul_le_mul_of_nonneg_left ha.1 (by positivity : 0 ≤ 6*S.intercept)
    linarith only [hgap.1,hm]
  have hnumhi : gapActual+6*S.intercept*S.amp P ≤ gap+6*S.intercept*a+258*g := by
    have hm := mul_le_mul_of_nonneg_left ha.2 (by positivity : 0 ≤ 6*S.intercept)
    have hi := mul_le_mul_of_nonneg_right hI1 hg.le
    nlinarith only [hgap.2,hm,hi]
  have hp : 0<6*S.price := mul_pos (by norm_num) S.price_pos
  have hprice : (1/50:ℝ) ≤ S.price := S.q_floor.trans S.q_le_price
  have hfee : (258*g)/(6*S.price) ≤ 2200*g := by
    apply (div_le_iff₀ hp).mpr
    have hgp := mul_le_mul_of_nonneg_left hprice hg.le
    nlinarith only [hgp,hg]
  constructor
  · exact div_le_div_of_nonneg_right hnumlo hp.le
  · calc delActual ≤ (gap+6*S.intercept*a+258*g)/(6*S.price) :=
        div_le_div_of_nonneg_right hnumhi hp.le
      _ = del+(258*g)/(6*S.price) := by rw [add_div]
      _ ≤ del+2200*g := add_le_add_right hfee _

end
end Cycle153
#print axioms Cycle153.rounded_deletion_bounds
