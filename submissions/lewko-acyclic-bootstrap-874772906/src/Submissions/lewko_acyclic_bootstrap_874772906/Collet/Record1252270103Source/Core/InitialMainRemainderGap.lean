/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual downward affine source budget pays the six MAIN enlargement
powers before any slot count. Positive raw scales below one remain allowed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalLowGuard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open Record1252270103Finite Record1252270103StepScalar

/-- Scaling the literal node gate retains three allowances after the width
rounding. No energy estimate or old endpoint hypothesis is used. -/
theorem node_amplification_gap (K : ℚ) (n low : Source) (b width A D : ℝ)
    (hg : RealGeometry K n low b) (he : 0≤(n.allowance:ℝ))
    (hL : 0≤(n.L:ℝ)) (hB : (low.B:ℝ)≤1) (hD : 0≤D)
    (hw : width≤PhysicalLowGuard.step n)
    (hA : A≤D*(sourceTReal n b+b+(n.L:ℝ)*width)) :
    A+6*(D*sourceAReal n low b)+3*D*(n.allowance:ℝ)≤D := by
  have hstep : 0≤PhysicalLowGuard.step n:=by
    dsimp only [PhysicalLowGuard.step]
    positivity
  have hwidth := PhysicalLowGuard.step_budget n he hL width 0 0 0 0 hw hstep hstep hstep hstep
  simp only [add_zero,mul_zero] at hwidth
  have hF : 0≤sourceFReal n low b := by
    dsimp only [sourceFReal]
    linarith [hg.a_small]
  have hB' := mul_le_mul_of_nonneg_right hB hF
  have hnode : sourceTReal n b+b+(n.L:ℝ)*width+6*sourceAReal n low b+
      3*(n.allowance:ℝ)≤1 := by
    have hp:=hg.parent_budget_room
    dsimp only [sourceFReal] at hB' hp
    linarith only [hp,hB',hwidth]
  have hh:=mul_le_mul_of_nonneg_left hnode hD
  nlinarith only [hh,hA]

section Initial
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal HeckeFamily.O) [NeZero rayM]
local instance initialMainGapFiniteQuotient : Finite (HeckeFamily.O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (HeckeFamily.O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal HeckeFamily.O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

theorem initial_log_volume_node_bound (n : Source) (b width : ℝ) (hZ1 : 1<Z)
    (hL : 0≤(n.L:ℝ))
    (hadm : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hlo : b-(n.allowance:ℝ)-width≤∑i,w i) (hhi : (∑i,w i)≤b) :
    Real.logb Z (volume (s))≤sourceTReal n b+b+(n.L:ℝ)*width := by
  have hv:=initialInput_volume_le_clipped rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hZ1
  have hexp : Real.logb Z (volume (s))≤length Z X₁+length Z X₂+(∑i,w i) := by
    have hh:=Real.logb_le_logb_of_le hZ1 (volume_pos (s)) hv
    simpa only [Real.logb_rpow hZ hZ1.ne'] using hh
  have hb : length Z X₁+length Z X₂+(n.L:ℝ)*(∑i,w i)≤(n.B:ℝ) := by
    simpa only [globalFace,mul_one] using hadm.2.2.2.2.2.2
  have hh:=mul_le_mul_of_nonneg_left hlo hL
  dsimp only [sourceTReal]
  linarith only [hexp,hb,hh,hhi]

/-- Actual initial volume, actual source face and actual width cell give the
needed positive gap; it is not inferred from the weaker volume <= Z cap. -/
theorem initial_main_amplification_gap (K : ℚ) (n low : Source) (b width : ℝ)
    (hZ1 : 1<Z) (hg : RealGeometry K n low b)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ)) (hB : (low.B:ℝ)≤1)
    (hw : width≤PhysicalLowGuard.step n)
    (hadm : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hlo : b-(n.allowance:ℝ)-width≤∑i,w i) (hhi : (∑i,w i)≤b) :
    Real.logb Z (volume (s))+6*sourceAReal n low b+3*(n.allowance:ℝ)≤1 := by
  have hv:=initial_log_volume_node_bound rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
    p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod n b width hZ1 hL hadm hlo hhi
  simpa only [one_mul,mul_one] using node_amplification_gap K n low b width
    (Real.logb Z (volume (s))) 1 hg he hL hB (by norm_num) hw (by simpa using hv)
end Initial
end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.node_amplification_gap
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_log_volume_node_bound
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_main_amplification_gap
