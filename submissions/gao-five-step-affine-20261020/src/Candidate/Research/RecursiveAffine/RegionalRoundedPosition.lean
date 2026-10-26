/- Copyright (c) 2026 Hailey Collet; modifications (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalLedger

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Cycle153
noncomputable section
open Cycle63.Optimization

def roundUp (g x : ℝ) : ℝ := (⌈x/g⌉ : ℝ)*g
def roundDown (g x : ℝ) : ℝ := (⌊x/g⌋ : ℝ)*g

theorem roundUp_bounds {g : ℝ} (hg : 0<g) (x : ℝ) : x≤roundUp g x ∧ roundUp g x≤x+g := by
  constructor
  · unfold roundUp
    calc x=(x/g)*g := by field_simp
      _≤(⌈x/g⌉ : ℝ)*g := mul_le_mul_of_nonneg_right (Int.le_ceil _) hg.le
  · unfold roundUp
    calc (⌈x/g⌉ : ℝ)*g≤(x/g+1)*g := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one _).le hg.le
      _=x+g := by field_simp

theorem roundDown_bounds {g : ℝ} (hg : 0<g) (x : ℝ) : x-g≤roundDown g x ∧ roundDown g x≤x := by
  constructor
  · unfold roundDown
    calc x-g=(x/g-1)*g := by field_simp
      _≤(⌊x/g⌋ : ℝ)*g := mul_le_mul_of_nonneg_right (by linarith [Int.lt_floor_add_one (x/g)]) hg.le
  · unfold roundDown
    calc (⌊x/g⌋ : ℝ)*g≤(x/g)*g := mul_le_mul_of_nonneg_right (Int.floor_le _) hg.le
      _=x := by field_simp

def roundedPosition (g B n₁ n₂ z : ℝ) : RegionalPosition where
  B := roundUp g B
  slotTop := roundUp g z
  mesh := g
  windowBottom := roundDown g (min n₁ n₂)
  sumBottom := roundDown g (n₁+n₂)
  plainLossCap := max 0 (max (1/4-roundDown g (min n₁ n₂))
    (1/4-(roundDown g (n₁+n₂)-(9/2)*roundUp g z-1/100)/2))

/-- Rounding a genuine state to a finite position preserves its native
plain window, rather than postulating that the state is on a grid. -/
theorem roundedPosition_window {S : RegionalStage} {g B n₁ n₂ z : ℝ}
    (hg : 0<g) (hz : 0≤z) (hp : n₁+n₂+S.lam*z≤B) :
    PlainWindow (roundedPosition g B n₁ n₂ z).windowBottom
      (roundedPosition g B n₁ n₂ z).sumBottom
      ((roundedPosition g B n₁ n₂ z).slotTop-g)
      (roundedPosition g B n₁ n₂ z).slotTop S.lam
      (roundedPosition g B n₁ n₂ z).B n₁ n₂ z := by
  have hm := (roundDown_bounds hg (min n₁ n₂)).2
  have hs := (roundDown_bounds hg (n₁+n₂)).2
  have hz' := roundUp_bounds hg z
  exact ⟨hm.trans (min_le_left _ _), hm.trans (min_le_right _ _), hs,
    by dsimp [roundedPosition]; linarith, hz'.1, hp.trans (roundUp_bounds hg B).1⟩

/-- The only rounding cost in the native affine amplifier is a bounded
linear perturbation. This holds for a fixed regional plane as well as a
terminal plane through the actual child. -/
theorem rounded_amplifier_bounds (S : RegionalStage) {g B n₁ n₂ z : ℝ}
    (hg : 0<g) (hK : amplifierRatio S.price S.intercept S.q≤7) :
    let a := planeAmplifier S.price S.intercept S.q S.lam B z
    a≤S.amp (roundedPosition g B n₁ n₂ z) ∧
      S.amp (roundedPosition g B n₁ n₂ z)≤a+42*g := by
  have hB := roundUp_bounds hg B
  have hz := roundUp_bounds hg z
  have hK0 : 0≤amplifierRatio S.price S.intercept S.q := by
    unfold amplifierRatio
    exact div_nonneg S.q_pos.le (by nlinarith [S.q_intercept_lt_price])
  have hc0 : 0≤6*S.price-S.lam := by linarith [S.lam_le_six_price]
  have hc5 : 6*S.price-S.lam≤5 := by linarith [S.price_le_one, S.one_le_lam]
  have hzlo := mul_le_mul_of_nonneg_left hz.1 hc0
  have hzhi := mul_le_mul_of_nonneg_left hz.2 hc0
  have hcg := mul_le_mul_of_nonneg_right hc5 hg.le
  have hlinear : 0≤roundUp g B-B+(6*S.price-S.lam)*(roundUp g z-z) := by nlinarith
  have hlinear' : roundUp g B-B+(6*S.price-S.lam)*(roundUp g z-z)≤6*g := by nlinarith
  have he := mul_le_mul hK hlinear' hlinear (by norm_num : (0:ℝ)≤7)
  dsimp only [RegionalStage.amp, roundedPosition, planeAmplifier]
  constructor <;> nlinarith [mul_nonneg hK0 hlinear]

theorem rounded_total_bounds (S : RegionalStage) {g B n₁ n₂ z : ℝ}
    (hg : 0<g) (hlam : S.lam≤5) :
    S.totalA (roundedPosition g B n₁ n₂ z) ≤ B-(S.lam-1)*z+5*g := by
  have hB := roundUp_bounds hg B
  have hz := roundUp_bounds hg z
  have hc : 0≤S.lam-1 := by linarith [S.one_le_lam]
  have he := mul_le_mul_of_nonneg_left hz.1 hc
  have hg' := mul_le_mul_of_nonneg_right hlam hg.le
  dsimp only [RegionalStage.totalA, roundedPosition, planeTotalLength]
  nlinarith

/-- The scalar native-domain gates imply all facts of the rounded affine
ledger. Each gate has a uniform margin eta; mesh costs at most 500g.
No returned-source estimate is assumed here. -/
theorem roundedPosition_facts (S : RegionalStage) {g eta B n₁ n₂ z A a : ℝ}
    (hg : 0<g) (heta : 0<eta) (hgrid : 500*g≤eta) (hetacap : eta≤1/1000)
    (hK : amplifierRatio S.price S.intercept S.q≤7) (hlam : S.lam≤5)
    (hz : 0≤z) (hzcap : z≤1-eta) (hB : B≤1-eta)
    (hplane : n₁+n₂+S.lam*z≤B)
    (hA : A=n₁+n₂+z) (ha : a=planeAmplifier S.price S.intercept S.q S.lam B z)
    (hbalanced : |n₁-n₂|≤6*slotPrice*z+1/100)
    (hactive : 0<n₁+n₂+6*slotPrice*z-1)
    (hamp : eta≤a)
    (hfirst : eta≤(S.primeFraction-1/2)*a-
      (B-1+(6*slotPrice-S.lam)*z)/6-lowReserveAt S.price S.intercept S.q)
    (hshort : eta≤(A-(1+6*slotPrice)*z-1/100)/2)
    (hcomparison : eta≤(A-(11/2)*z-1/100)/2)
    (hfixed0 : eta≤1-(B-(S.lam-1)*z)-4*a-1/50)
    (hfixed1 : eta≤1-(B-(S.lam-1)*z)-4*a-1/50-
      (2/3)*(51/200-A/2+(1+6*slotPrice)*z/2))
    (hfixed2 : eta≤1-(B-(S.lam-1)*z)-4*a-1/50-
      (2/3)*(51/200-A/2+(11/4)*z))
    (hexception0 : eta≤1-(B-(S.lam-1)*z)-(9/2)*a-1/50)
    (hexception1 : eta≤1-(B-(S.lam-1)*z)-(9/2)*a-1/50-
      (2/3)*(51/200-A/2+(1+6*slotPrice)*z/2))
    (hexception2 : eta≤1-(B-(S.lam-1)*z)-(9/2)*a-1/50-
      (2/3)*(51/200-A/2+(11/4)*z))
    (hzero : eta≤1-(B-(S.lam-1)*z)-6*a-1/380-S.zeroSaving)
    (hcapA : 0≤B-(S.lam-1)*z) :
    (roundedPosition g B n₁ n₂ z).Facts S := by
  let P := roundedPosition g B n₁ n₂ z
  have hku := slotPrice_mem
  have hmin : (A-(1+6*slotPrice)*z-1/100)/2≤min n₁ n₂ := by
    obtain ⟨hbal1,hbal2⟩ := abs_le.mp hbalanced
    apply le_min <;> linarith
  have hw := roundDown_bounds hg (min n₁ n₂)
  have hs := roundDown_bounds hg (n₁+n₂)
  have hz' := roundUp_bounds hg z
  have hB' := roundUp_bounds hg B
  have ha' := rounded_amplifier_bounds S (B:=B) (z:=z) (n₁:=n₁) (n₂:=n₂) hg hK
  rw [←ha] at ha'
  change a≤S.amp P ∧ S.amp P≤a+42*g at ha'
  have hAt := rounded_total_bounds S (B:=B) (n₁:=n₁) (n₂:=n₂) (z:=z) hg hlam
  change S.totalA P≤B-(S.lam-1)*z+5*g at hAt
  have hL1 : 1/4-P.windowBottom≤51/200-A/2+(1+6*slotPrice)*z/2+g := by
    dsimp only [P, roundedPosition]
    linarith
  have hL2 : 1/4-(P.sumBottom-(9/2)*P.slotTop-1/100)/2≤
      51/200-A/2+(11/4)*z+3*g := by
    dsimp only [P, roundedPosition]
    linarith
  have hL : P.plainLossCap≤max 0
      (max (51/200-A/2+(1+6*slotPrice)*z/2)
           (51/200-A/2+(11/4)*z))+3*g := by
    have h0 : (0:ℝ)≤max 0 (max (51/200-A/2+(1+6*slotPrice)*z/2)
      (51/200-A/2+(11/4)*z)) := le_max_left _ _
    have h1 : 51/200-A/2+(1+6*slotPrice)*z/2≤max 0
      (max (51/200-A/2+(1+6*slotPrice)*z/2) (51/200-A/2+(11/4)*z)) :=
      le_max_of_le_right (le_max_left _ _)
    have h2 : 51/200-A/2+(11/4)*z≤max 0
      (max (51/200-A/2+(1+6*slotPrice)*z/2) (51/200-A/2+(11/4)*z)) :=
      le_max_of_le_right (le_max_right _ _)
    dsimp only [P, roundedPosition]
    apply max_le (by linarith)
    apply max_le <;> linarith
  have hfixed : eta≤1-(B-(S.lam-1)*z)-4*a-1/50-
      (2/3)*max 0 (max (51/200-A/2+(1+6*slotPrice)*z/2) (51/200-A/2+(11/4)*z)) := by
    rcases le_total (51/200-A/2+(1+6*slotPrice)*z/2) (51/200-A/2+(11/4)*z) with h|h
    · rw [max_eq_right h]
      rcases le_total 0 (51/200-A/2+(11/4)*z) with h|h
      · rwa [max_eq_right h]
      · rw [max_eq_left h]; linarith
    · rw [max_eq_left h]
      rcases le_total 0 (51/200-A/2+(1+6*slotPrice)*z/2) with h|h
      · rwa [max_eq_right h]
      · rw [max_eq_left h]; linarith
  have hexc : eta≤1-(B-(S.lam-1)*z)-(9/2)*a-1/50-
      (2/3)*max 0 (max (51/200-A/2+(1+6*slotPrice)*z/2) (51/200-A/2+(11/4)*z)) := by
    rcases le_total (51/200-A/2+(1+6*slotPrice)*z/2) (51/200-A/2+(11/4)*z) with h|h
    · rw [max_eq_right h]
      rcases le_total 0 (51/200-A/2+(11/4)*z) with h|h
      · rwa [max_eq_right h]
      · rw [max_eq_left h]; linarith
    · rw [max_eq_left h]
      rcases le_total 0 (51/200-A/2+(1+6*slotPrice)*z/2) with h|h
      · rwa [max_eq_right h]
      · rw [max_eq_left h]; linarith
  have hgap : 0<S.oldGap P := by
    have hc : 0≤6*slotPrice-S.lam := by linarith [S.lam_le_six_old]
    have hzlo := mul_le_mul_of_nonneg_left hz'.1 hc
    dsimp only [RegionalStage.oldGap, P, roundedPosition, planeGap]
    linarith [hactive]
  have hfirst' : lowReserveAt S.price S.intercept S.q≤
      (S.primeFraction-1/2)*S.amp P-S.oldGap P/6 := by
    have hc : 0≤6*slotPrice-S.lam := by linarith [S.lam_le_six_old]
    have hc' : 6*slotPrice-S.lam≤4 := by linarith [S.one_le_lam, hku.2]
    have hzup := mul_le_mul_of_nonneg_left hz'.2 hc
    have hcg := mul_le_mul_of_nonneg_right hc' hg.le
    have hp : 0≤S.primeFraction-1/2 := by linarith [S.primeFraction_half]
    have hamplo := mul_le_mul_of_nonneg_left ha'.1 hp
    have hgapup : S.oldGap P≤B-1+(6*slotPrice-S.lam)*z+5*g := by
      dsimp only [RegionalStage.oldGap, P, roundedPosition, planeGap]
      nlinarith
    linarith only [hfirst, hamplo, hgapup, hgrid, hg]
  refine ⟨hg, ?_, ?_, ?_, le_max_left _ _, ?_, ?_, ?_, ?_, hgap,
    by linarith [ha'.1], ?_, hfirst', ?_, ?_, ?_⟩
  · show roundUp g z≤1
    linarith
  · show 0<roundDown g (min n₁ n₂)
    linarith
  · show roundUp g B≤1
    linarith
  · show 1/100+(9/2)*roundUp g z≤roundDown g (n₁+n₂)
    linarith
  · show 1≤roundDown g (n₁+n₂)+(9/2)*(roundUp g z-g)+1/100
    have hκz : 6*slotPrice*z≤(9/2)*z := by nlinarith [hku.2]
    linarith
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_right _ _)
  · linarith [ha'.2, S.zeroSaving_pos]
  · change 1/50+2/3*P.plainLossCap≤1-S.totalA P-4*S.amp P
    linarith only [hfixed, hL, hAt, ha'.2, hgrid, hg]
  · change 1/50+2/3*P.plainLossCap≤1-S.totalA P-(9/2)*S.amp P
    linarith only [hexc, hL, hAt, ha'.2, hgrid, hg]
  · linarith [ha'.2]

end
end Cycle153

#print axioms Cycle153.roundedPosition_facts
