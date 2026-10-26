/- Fixed paid certificate margins at actual rounded regional sources. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.NormalizedPosition

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

def positionMargin : ℝ := 1/10000000000

def sourceGate (j : Fin 4) (k : Fin 10) : Fin 62 := ⟨16*j.val+k.val,by omega⟩

def sourceUnitGate (j : Fin 4) : Fin 62 := ![11,27,43,58] j

def gateValue (j : Fin 4) (k : Fin 10) (x : Fin 14 → ℝ) : ℝ :=
  ![![Coordinates.gate1_first_error x, Coordinates.gate1_zero x, Coordinates.gate1_short_positive x, Coordinates.gate1_comparison_positive x, Coordinates.gate1_fixed_0 x, Coordinates.gate1_exceptional_0 x, Coordinates.gate1_fixed_1 x, Coordinates.gate1_exceptional_1 x, Coordinates.gate1_fixed_2 x, Coordinates.gate1_exceptional_2 x],
    ![Coordinates.gate2_first_error x, Coordinates.gate2_zero x, Coordinates.gate2_short_positive x, Coordinates.gate2_comparison_positive x, Coordinates.gate2_fixed_0 x, Coordinates.gate2_exceptional_0 x, Coordinates.gate2_fixed_1 x, Coordinates.gate2_exceptional_1 x, Coordinates.gate2_fixed_2 x, Coordinates.gate2_exceptional_2 x],
    ![Coordinates.gate3_first_error x, Coordinates.gate3_zero x, Coordinates.gate3_short_positive x, Coordinates.gate3_comparison_positive x, Coordinates.gate3_fixed_0 x, Coordinates.gate3_exceptional_0 x, Coordinates.gate3_fixed_1 x, Coordinates.gate3_exceptional_1 x, Coordinates.gate3_fixed_2 x, Coordinates.gate3_exceptional_2 x],
    ![Coordinates.gate4_first_error x, Coordinates.gate4_zero x, Coordinates.gate4_short_positive x, Coordinates.gate4_comparison_positive x, Coordinates.gate4_fixed_0 x, Coordinates.gate4_exceptional_0 x, Coordinates.gate4_fixed_1 x, Coordinates.gate4_exceptional_1 x, Coordinates.gate4_fixed_2 x, Coordinates.gate4_exceptional_2 x]] j k

def modelCap (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.capA1 x,Coordinates.capA2 x,Coordinates.capA3 x,Coordinates.capA4 x] j

def modelAmplification (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.a1 x,Coordinates.a2 x,Coordinates.a3 x,Coordinates.a4 x] j

def previousIntercept (j : Fin 4) : ℝ :=
  ![Coordinates.inner0,Coordinates.inner1,Coordinates.inner2,Coordinates.inner3] j

def rawPlane (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.inner0*Coordinates.U1 x,Coordinates.inner1*Coordinates.U2 x,
    Coordinates.inner2*Coordinates.U3 x,
    Coordinates.A4 x+((innerStage 3).lam-1)*Coordinates.z4 x] j

theorem sourceGate_depth (j : Fin 4) (k : Fin 10) : gateDepth (sourceGate j k) = j.val+1 := by
  fin_cases j <;> fin_cases k <;> rfl

theorem sourceUnitGate_depth (j : Fin 4) : gateDepth (sourceUnitGate j) = j.val+1 := by
  fin_cases j <;> rfl

theorem sourceGate_meaning (j : Fin 4) (k : Fin 10) (x : Fin 14 → ℝ) :
    Coordinates.objectives (sourceGate j k) x = gateValue j k x := by
  fin_cases j <;> fin_cases k <;> rfl

theorem sourceUnitGate_meaning (j : Fin 4) (x : Fin 14 → ℝ) :
    Coordinates.objectives (sourceUnitGate j) x = modelUnit j x := by
  fin_cases j <;> rfl

theorem sourceGate_margin {j : Fin 4} {x : Fin 14 → ℝ} (h : PrefixRows (j.val+1) x)
    (k : Fin 10) : positionMargin < gateValue j k x := by
  have hg := prefix_gate h (sourceGate j k) (le_of_eq (sourceGate_depth j k))
  rw [sourceGate_meaning] at hg
  norm_num only [positionMargin] at *
  linarith only [hg]

theorem sourceUnit_positive {j : Fin 4} {x : Fin 14 → ℝ} (h : PrefixRows (j.val+1) x) :
    0 < modelUnit j x := by
  have hg := prefix_gate h (sourceUnitGate j) (le_of_eq (sourceUnitGate_depth j))
  rw [sourceUnitGate_meaning] at hg
  linarith only [hg]

theorem inner_stage_ratio (j : Fin 4) :
    amplifierRatio (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q ≤ 7 := by
  fin_cases j
  exact Cycle153.FixedStages.stage1_ratio_bound
  exact Cycle153.FixedStages.stage2_ratio_bound
  exact Cycle153.FixedStages.stage3_ratio_bound
  exact Cycle153.FixedStages.stage4_ratio_bound

theorem inner_stage_slope (j : Fin 4) : (innerStage j.val).lam ≤ 5 := by
  fin_cases j
  exact Cycle153.FixedStages.stage1_slope_bound
  exact Cycle153.FixedStages.stage2_slope_bound
  exact Cycle153.FixedStages.stage3_slope_bound
  exact Cycle153.FixedStages.stage4_slope_bound

theorem previousIntercept_cap (j : Fin 4) : previousIntercept j ≤ 1-positionMargin := by
  fin_cases j <;> norm_num [previousIntercept,positionMargin,Coordinates.inner0,
    Coordinates.inner1,Coordinates.inner2,Coordinates.inner3]

macro "fixed_model_identity" : tactic => `(tactic| (norm_num [innerStage, modelUnit, modelLength, modelSlots, modelCap, modelAmplification, rawPlane, gateValue, Cycle153.FixedStages.stage1, Cycle153.FixedStages.stage2, Cycle153.FixedStages.stage3, Cycle153.FixedStages.stage4, Coordinates.q0, Coordinates.q1, Coordinates.q2, Coordinates.q3, Coordinates.q4, Coordinates.k0, Coordinates.k1, Coordinates.k2, Coordinates.k3, Coordinates.k4, Coordinates.inner0, Coordinates.inner1, Coordinates.inner2, Coordinates.inner3, Coordinates.inner4, Coordinates.alpha, Coordinates.kappa, slotPrice, betaBound, amplifierRatio, lowReserveAt, lowReserveWeight, allowanceUnit, Coordinates.a1, Coordinates.gap1, Coordinates.capA1, Coordinates.oldcap1, Coordinates.lowres1, Coordinates.a2, Coordinates.gap2, Coordinates.capA2, Coordinates.oldcap2, Coordinates.lowres2, Coordinates.a3, Coordinates.gap3, Coordinates.capA3, Coordinates.oldcap3, Coordinates.lowres3, Coordinates.a4, Coordinates.gap4, Coordinates.capA4, Coordinates.oldcap4, Coordinates.lowres4, Coordinates.gate1_first_error, Coordinates.gate1_zero, Coordinates.gate1_short_positive, Coordinates.gate1_comparison_positive, Coordinates.gate1_fixed_0, Coordinates.gate1_exceptional_0, Coordinates.gate1_fixed_1, Coordinates.gate1_exceptional_1, Coordinates.gate1_fixed_2, Coordinates.gate1_exceptional_2, Coordinates.gate2_first_error, Coordinates.gate2_zero, Coordinates.gate2_short_positive, Coordinates.gate2_comparison_positive, Coordinates.gate2_fixed_0, Coordinates.gate2_exceptional_0, Coordinates.gate2_fixed_1, Coordinates.gate2_exceptional_1, Coordinates.gate2_fixed_2, Coordinates.gate2_exceptional_2, Coordinates.gate3_first_error, Coordinates.gate3_zero, Coordinates.gate3_short_positive, Coordinates.gate3_comparison_positive, Coordinates.gate3_fixed_0, Coordinates.gate3_exceptional_0, Coordinates.gate3_fixed_1, Coordinates.gate3_exceptional_1, Coordinates.gate3_fixed_2, Coordinates.gate3_exceptional_2, Coordinates.gate4_first_error, Coordinates.gate4_zero, Coordinates.gate4_short_positive, Coordinates.gate4_comparison_positive, Coordinates.gate4_fixed_0, Coordinates.gate4_exceptional_0, Coordinates.gate4_fixed_1, Coordinates.gate4_exceptional_1, Coordinates.gate4_fixed_2, Coordinates.gate4_exceptional_2, Coordinates.loss1_0, Coordinates.loss1_1, Coordinates.loss1_2, Coordinates.loss2_0, Coordinates.loss2_1, Coordinates.loss2_2, Coordinates.loss3_0, Coordinates.loss3_1, Coordinates.loss3_2, Coordinates.loss4_0, Coordinates.loss4_1, Coordinates.loss4_2] <;> ring))

theorem modelCap_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    modelCap j x = rawPlane j x-((innerStage j.val).lam-1)*modelSlots j x := by
  fin_cases j <;> fixed_model_identity

theorem modelAmplification_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    modelAmplification j x =
      amplifierRatio (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q*
        (rawPlane j x-(innerStage j.val).intercept*modelUnit j x+
          (6*(innerStage j.val).price-(innerStage j.val).lam)*modelSlots j x)+
        lowReserveWeight*modelUnit j x := by
  fin_cases j <;> fixed_model_identity

theorem firstGate_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 0 x = ((innerStage j.val).primeFraction-1/2)*modelAmplification j x-
      (rawPlane j x-modelUnit j x+(6*slotPrice-(innerStage j.val).lam)*modelSlots j x)/6-
      lowReserveAt (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q*modelUnit j x := by
  fin_cases j <;> fixed_model_identity

theorem zeroGate_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 1 x = modelUnit j x-modelCap j x-6*modelAmplification j x-
      (1/380+(innerStage j.val).zeroSaving)*modelUnit j x := by
  fin_cases j <;> fixed_model_identity

theorem shortGate_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 2 x = (modelLength j x-(1+6*slotPrice)*modelSlots j x-modelUnit j x/100)/2 := by
  fin_cases j <;> fixed_model_identity

theorem comparisonGate_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 3 x = (modelLength j x-(11/2)*modelSlots j x-modelUnit j x/100)/2 := by
  fin_cases j <;> fixed_model_identity

theorem channelGate4_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 4 x = modelUnit j x-modelCap j x-4*modelAmplification j x-
      modelUnit j x/50-(2/3)*(0) := by
  fin_cases j <;> fixed_model_identity

theorem channelGate5_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 5 x = modelUnit j x-modelCap j x-(9/2)*modelAmplification j x-
      modelUnit j x/50-(2/3)*(0) := by
  fin_cases j <;> fixed_model_identity

theorem channelGate6_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 6 x = modelUnit j x-modelCap j x-4*modelAmplification j x-
      modelUnit j x/50-(2/3)*((51/200)*modelUnit j x-modelLength j x/2+(1+6*slotPrice)*modelSlots j x/2) := by
  fin_cases j <;> fixed_model_identity

theorem channelGate7_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 7 x = modelUnit j x-modelCap j x-(9/2)*modelAmplification j x-
      modelUnit j x/50-(2/3)*((51/200)*modelUnit j x-modelLength j x/2+(1+6*slotPrice)*modelSlots j x/2) := by
  fin_cases j <;> fixed_model_identity

theorem channelGate8_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 8 x = modelUnit j x-modelCap j x-4*modelAmplification j x-
      modelUnit j x/50-(2/3)*((51/200)*modelUnit j x-modelLength j x/2+(11/4)*modelSlots j x) := by
  fin_cases j <;> fixed_model_identity

theorem channelGate9_identity (j : Fin 4) (x : Fin 14 → ℝ) :
    gateValue j 9 x = modelUnit j x-modelCap j x-(9/2)*modelAmplification j x-
      modelUnit j x/50-(2/3)*((51/200)*modelUnit j x-modelLength j x/2+(11/4)*modelSlots j x) := by
  fin_cases j <;> fixed_model_identity

theorem rawPlane_le_previous (j : Fin 4) (x : Fin 14 → ℝ)
    (hterminal : j.val=3 → modelLength j x+(6*Coordinates.k3-1)*modelSlots j x ≤
      Coordinates.inner3*modelUnit j x) :
    rawPlane j x ≤ previousIntercept j*modelUnit j x := by
  fin_cases j
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · convert hterminal rfl using 1 <;>
      norm_num [rawPlane,modelLength,modelSlots,modelUnit,previousIntercept,innerStage,
        Cycle153.FixedStages.stage4,Coordinates.k3]

theorem fixed_stage_rounded_facts (j : Fin 4) (x : Fin 14 → ℝ)
    (hp : PrefixRows (j.val+1) x) {g n1 n2 : ℝ}
    (hg : 0 < g) (hgrid : 500*g ≤ positionMargin)
    (hU1 : modelUnit j x ≤ 1) (hz : 0 ≤ modelSlots j x)
    (hA : modelLength j x=n1+n2+modelSlots j x)
    (hregion : modelLength j x ≤ modelCap j x)
    (hterminal : j.val=3 → modelLength j x+(6*Coordinates.k3-1)*modelSlots j x ≤
      Coordinates.inner3*modelUnit j x)
    (hbalanced : |n1-n2| ≤ 6*slotPrice*modelSlots j x+modelUnit j x/100)
    (hactive : 0 < modelLength j x+(6*slotPrice-1)*modelSlots j x-modelUnit j x) :
    (Cycle153.roundedPosition g (rawPlane j x/modelUnit j x)
      (n1/modelUnit j x) (n2/modelUnit j x) (modelSlots j x/modelUnit j x)).Facts (innerStage j.val) := by
  have hU := sourceUnit_positive hp
  have hUne : modelUnit j x ≠ 0 := ne_of_gt hU
  have hmargin : 0 < positionMargin := by norm_num [positionMargin]
  have hB : rawPlane j x ≤ (1-positionMargin)*modelUnit j x :=
    (rawPlane_le_previous j x hterminal).trans
      (mul_le_mul_of_nonneg_right (previousIntercept_cap j) hU.le)
  have hfirst := sourceGate_margin hp (0:Fin 10)
  have hzero := sourceGate_margin hp (1:Fin 10)
  have hshort := sourceGate_margin hp (2:Fin 10)
  have hcomparison := sourceGate_margin hp (3:Fin 10)
  have hfixed0 := sourceGate_margin hp (4:Fin 10)
  have hexception0 := sourceGate_margin hp (5:Fin 10)
  have hfixed1 := sourceGate_margin hp (6:Fin 10)
  have hexception1 := sourceGate_margin hp (7:Fin 10)
  have hfixed2 := sourceGate_margin hp (8:Fin 10)
  have hexception2 := sourceGate_margin hp (9:Fin 10)
  rw [firstGate_identity] at hfirst
  rw [zeroGate_identity] at hzero
  rw [shortGate_identity] at hshort
  rw [comparisonGate_identity] at hcomparison
  rw [channelGate4_identity] at hfixed0
  rw [channelGate5_identity] at hexception0
  rw [channelGate6_identity] at hfixed1
  rw [channelGate7_identity] at hexception1
  rw [channelGate8_identity] at hfixed2
  rw [channelGate9_identity] at hexception2
  have hcap := modelCap_identity j x
  have hcaple : modelCap j x ≤ rawPlane j x := by
    have hprod := mul_nonneg (sub_nonneg.mpr (innerStage j.val).one_le_lam) hz
    linarith only [hcap,hprod]
  have hApos : 0 < modelLength j x := by linarith only [hcomparison,hz,hU,hmargin]
  have hcap0 : 0 ≤ modelCap j x := hApos.le.trans hregion
  have hzA : modelSlots j x ≤ modelLength j x := by linarith only [hcomparison,hz,hU,hmargin]
  have hzcap : modelSlots j x ≤ (1-positionMargin)*modelUnit j x :=
    hzA.trans (hregion.trans (hcaple.trans hB))
  have hplane : n1+n2+(innerStage j.val).lam*modelSlots j x ≤ rawPlane j x := by
    nlinarith only [hA,hregion,hcap]
  have hold : 0 < rawPlane j x-modelUnit j x+
      (6*slotPrice-(innerStage j.val).lam)*modelSlots j x := by
    nlinarith only [hactive,hregion,hcap]
  have hres : 0 ≤ lowReserveAt (innerStage j.val).price (innerStage j.val).intercept
      (innerStage j.val).q*modelUnit j x := by
    have hqI := (div_lt_one (innerStage j.val).price_pos).mpr
      (innerStage j.val).q_intercept_lt_price
    have hr : 0 ≤ lowReserveAt (innerStage j.val).price (innerStage j.val).intercept
        (innerStage j.val).q := by
      unfold lowReserveAt
      exact mul_nonneg lowReserveWeight_pos.le (by linarith only [hqI])
    exact mul_nonneg hr hU.le
  have hprime : (innerStage j.val).primeFraction-1/2=(49/100:ℝ) := by
    fin_cases j <;> norm_num [innerStage,Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
      Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4]
  have hamp : positionMargin ≤ modelAmplification j x := by
    rw [hprime] at hfirst
    linarith only [hfirst,hold,hres,hmargin]
  have ha : modelAmplification j x/modelUnit j x =
      planeAmplifier (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q
        (innerStage j.val).lam (rawPlane j x/modelUnit j x) (modelSlots j x/modelUnit j x) := by
    rw [modelAmplification_identity]
    unfold planeAmplifier
    field_simp [hUne]
    <;> ring
  exact Cycle153.normalized_roundedPosition_facts (innerStage j.val) hg hmargin hgrid
    (by norm_num [positionMargin]) hU hU1 (inner_stage_ratio j) (inner_stage_slope j)
    hz hzcap hB hplane hA hcap hcap0 ha hbalanced hactive hamp hfirst.le hshort.le
    hcomparison.le (by simpa only [mul_zero,sub_zero] using hfixed0.le)
    hfixed1.le hfixed2.le (by simpa only [mul_zero,sub_zero] using hexception0.le)
    hexception1.le hexception2.le hzero.le

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.sourceGate_margin
#print axioms OAI.SevenEighths.Cycle153Reachable.modelAmplification_identity
#print axioms OAI.SevenEighths.Cycle153Reachable.channelGate9_identity

#print axioms OAI.SevenEighths.Cycle153Reachable.fixed_stage_rounded_facts
