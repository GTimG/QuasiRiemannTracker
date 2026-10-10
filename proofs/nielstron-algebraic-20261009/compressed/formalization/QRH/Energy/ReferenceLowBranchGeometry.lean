import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry
import QRH.PlainReflectionGeometry
import QRH.Energy.ReferenceDeletionClipped

/-!
Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Energy/ReferenceLowBranchGeometry.lean. Original objects and hypotheses retained; new theorem names
extend κ to 13/18 and adjust reflection reserves. Must be kernel checked before
integration. The original source is imported unchanged.
-/
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget CenteredMomentEnergyReferenceDeletionCapacity
local notation "O"=>HeckeFamily.O

lemma slot_budgets_extended (M total ell kappa:ℝ)(_hM:0≤M)(hell:0≤ell)(hk:13/18≤kappa)
    (hlarge:5*M/6≤total+ell)(hcap:total+ell+(6*kappa-1)*ell≤M):
    ell≤M/20 ∧ (6*kappa-1)*ell≤M/6:=by
  exact QRH.PlainReflection.slot_budgets hell hk hlarge hcap


theorem reflected_low_extended (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤M)(_hs:0≤short)(hsM:short≤M/4)(_hell:0≤ell)(_hz:0≤z)(hze:z≤ell)
    (hk:13/18≤kappa)(he:ell≤M/20)(hbudget:(6*kappa-1)*ell≤M/6)(hxi:0≤xi)
    (hhigh:5*M/6<short+max 0 along+z)
    (href:reflected≤max 0 (M-along+xi)):
    0<along ∧ reflected+short+z≤23*M/30+xi ∧
      reflected+short+6*kappa*z≤14*M/15+xi:=by
  exact QRH.PlainReflection.reflected_low hM hsM hze hk he hbudget hxi hhigh href


theorem deleted_reference_cases_extended (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:13/18≤kappa)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤M) ∨
    (0<Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
      reflected+short+z≤23*M/30+xi ∧ reflected+short+6*kappa*z≤14*M/15+xi):=by
  dsimp only
  have hg:=balanced_reference_geometry_extended Z M X₁ X₂ ell kappa hZ hM hX₁ hX₂ hell hk hlarge hcap
  have hpos:=comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hlongpos:=div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0:=length_nonneg Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ)) hZ
  have hlong:length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))≤
      Real.logb Z (comparisonSecond Z M X₁ X₂):=by
    have hY:1≤comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
    have hdiv:=div_le_self hpos.2.le hn₂
    exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le hY hdiv)
  by_cases hlo:length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+
      length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6
  · refine Or.inl ⟨hlo,?_⟩
    have hzcap:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*kappa)
    rw [hg.2.2.2.1] at hlong
    nlinarith
  · apply Or.inr
    obtain ⟨he,hbudget⟩:=slot_budgets_extended M (Real.logb Z (X₁*X₂)) ell kappa hM hell hk hlarge hcap
    apply reflected_low_extended M _ _ ell z kappa xi reflected hM hshort0 hshort hell hz hze hk he hbudget hxi _ href
    rw [←length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo


lemma reflected_low_admissible_extended (M xi short reflected z kappa:ℝ)
    (hxi:xi≤M/15)(ht:reflected+short+z≤23*M/30+xi)
    (hc:reflected+short+6*kappa*z≤14*M/15+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤M:=by
  exact QRH.PlainReflection.reflected_low_admissible hxi ht hc

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI
