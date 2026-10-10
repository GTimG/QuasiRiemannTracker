/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceDeletionClipped.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
import Cycle25.Energy.ReferenceDeletionCapacity

import Cycle25.Energy.ReferenceState

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionClipped
open HeckeFamily Cycle25CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

lemma deleted_long_le_width (Z M X₁ X₂ ell kappa : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 7/10 ≤ kappa)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I) :
    Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) ≤ M := by
  have hg := balanced_reference_geometry Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap
  have hn := product_norm_ge_one D hD
  have hp : 0 < ((∏ I ∈ D, I).absNorm:ℝ) := zero_lt_one.trans_le hn
  have hy := (comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂).2
  rw [Real.logb_div hy.ne' hp.ne']
  have hlog := Real.logb_nonneg hZ hn
  linarith [hg.2.2.2.2]

lemma clipped_reflected_bound (Z M X₁ X₂ ell kappa xi reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 7/10 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (href : reflected ≤ max 0 (M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi)) :
    reflected ≤ M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi := by
  have hlong := deleted_long_le_width Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap D hD
  rwa [max_eq_right (by linarith)] at href

end SevenEighths.Cycle25CenteredMomentEnergyReferenceDeletionClipped

end

end OAI
