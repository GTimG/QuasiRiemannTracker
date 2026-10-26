/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The pre-cardinality node step pays the exceptional centered scalar's errors.
Only thresholds for fixed profile/cardinality constants may depend on N. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstScalar
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalLowGuard
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialMainRemainderGap

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open Filter Record1252270103Finite Record1252270103StepScalar
open OAI OAI.SevenEighths CenteredMomentSectorLocalization

theorem node_centered_error_guard (K : ℚ)(n low : Source)(b width frequency reserve loss : ℝ)
    (hg : RealGeometry K n low b)(he : 0≤(n.allowance:ℝ))(hL : 0≤(n.L:ℝ))
    (hf0 : 0≤frequency)(hr0 : 0≤reserve)
    (hw : width≤PhysicalLowGuard.step n)(hf : frequency≤PhysicalLowGuard.step n)
    (hr : reserve≤PhysicalLowGuard.step n)(hl : loss≤PhysicalLowGuard.step n) :
    (n.L:ℝ)*width+5*(frequency+reserve)/6+loss≤sourceAReal n low b := by
  have hs : 0≤PhysicalLowGuard.step n := by unfold PhysicalLowGuard.step;positivity
  have hh:=PhysicalLowGuard.step_budget n he hL width frequency reserve loss 0 hw hf hr hl hs
  have ha:=hg.a_allowance
  linarith

theorem eventually_centered_error_guard (n low : Source)(ξ reserve loss width : ℝ)
    (he : 0<(n.allowance:ℝ))(hL : 0≤(n.L:ℝ))(hξ : 0<ξ)
    (hξstep : ξ≤PhysicalLowGuard.step n)(hr0 : 0≤reserve)
    (hr : reserve≤PhysicalLowGuard.step n)(hl : loss≤PhysicalLowGuard.step n)
    (hw : width≤PhysicalLowGuard.step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(K : ℚ)(b : ℝ),RealGeometry K n low b →
      (n.L:ℝ)*width+5*(frequencyLoss Z 32 ξ+reserve)/6+loss≤sourceAReal n low b := by
  filter_upwards [OAI.SevenEighths.CenteredMomentFirstAmplificationChoice.eventually_frequency_loss 32 ξ
    (by norm_num) hξ] with Z hz
  exact ⟨hz.1,fun K b hg=>node_centered_error_guard K n low b width _ reserve loss
    hg he.le hL hz.2.1 hr0 hw (hz.2.2.le.trans hξstep) hr hl⟩

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.node_centered_error_guard
#print axioms QRH.Record1252270103Source.ExceptionalPrice.eventually_centered_error_guard
