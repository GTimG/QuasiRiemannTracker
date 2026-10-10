/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceState.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
import OAI.NumberTheory.DirichletL.Energy.ReferenceState
import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
import Cycle25.Energy.ReflectionRetainedLength

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

export CenteredMomentEnergyReferenceState
  (effectiveRadial radialEnergy_effective effectiveState effective_row_norm
    effective_character_nonprincipal effective_character_cap comparisonFirst comparisonSecond
    comparison_positive comparison_same_product comparison_second_power)

theorem balanced_reference_geometry (Z M X₁ X₂ ell κ:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:7/10≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M):
    ell≤5*M/96 ∧
    1≤comparisonFirst Z M ∧
    comparisonFirst Z M≤comparisonSecond Z M X₁ X₂ ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4 ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)≤M:=by
  have hkell:16/5*ell≤(6*κ-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  have he:ell≤5*M/96:=by linarith
  have hlen:M/2≤Real.logb Z (X₁*X₂):=by linarith
  have hupper:Real.logb Z (X₁*X₂)-M/4≤M:=by linarith
  have hlog:Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4:=by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,Real.logb_rpow]
    · exact zero_lt_one.trans hZ
    · exact hZ.ne'
  refine ⟨he,Real.one_le_rpow hZ.le (by linarith),?_,hlog,by rw [hlog];exact hupper⟩
  rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem balanced_reflection_margins (Z M X₁ X₂ ell κ ξ reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:7/10≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+ξ):
    reflected+M/4+ell≤37*M/48+ξ ∧
    reflected+M/4+ell+(6*κ-1)*ell≤15*M/16+ξ:=by
  have hlog:=(balanced_reference_geometry Z M X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hlarge hcap).2.2.2.1
  rw [hlog] at href
  have hc:=Cycle25CenteredMomentReflectionRetainedLength.positive_slot_width_drop M
    (Real.logb Z (X₁*X₂)+ell) ell ξ κ hM hell hκ hlarge hcap
  constructor <;> linarith [hc.1,hc.2]

end SevenEighths.Cycle25CenteredMomentEnergyReferenceState

end

end OAI
