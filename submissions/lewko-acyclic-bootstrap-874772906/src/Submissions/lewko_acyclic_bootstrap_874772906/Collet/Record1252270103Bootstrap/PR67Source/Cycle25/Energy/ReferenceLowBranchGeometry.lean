import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.ReferenceDeletionCapacity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.ReferenceState
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceLowBranchGeometry.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands Cycle25CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget Cycle25CenteredMomentEnergyReferenceDeletionCapacity
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤M)(hell:0≤ell)(hk:7/10≤kappa)
    (hlarge:5*M/6≤total+ell)(hcap:total+ell+(6*kappa-1)*ell≤M):
    ell≤5*M/96 ∧ (6*kappa-1)*ell≤M/6:=by
  have hkell:16/5*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤M)(_hs:0≤ short)(hsM:short≤M/4)(_hell:0≤ell)(_hz:0≤z)(hze:z≤ell)
    (hk:7/10≤kappa)(he:ell≤5*M/96)(hbudget:(6*kappa-1)*ell≤M/6)(hxi:0≤xi)
    (hhigh:5*M/6<short+max 0 along+z)
    (href:reflected≤ max 0 (M-along+xi)):
    0<along ∧ reflected+short+z≤37*M/48+xi ∧
      reflected+short+6*kappa*z≤15*M/16+xi:=by
  have haz:0<along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤5*M/96:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤M/16)(ht:reflected+short+z≤37*M/48+xi)
    (hc:reflected+short+6*kappa*z≤15*M/16+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤M:=by
  constructor <;> linarith

end SevenEighths.Cycle25CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI

end Record1252270103Bootstrap.PR67
