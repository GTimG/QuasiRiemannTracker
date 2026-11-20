/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.FixedCubeApplicationBad

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

/-- Supplying labels are the actual selected primes, with repeated labels
removed only in the finite bad-set product. The norm bound retains all slots. -/
def actualSupplyingLabels (p : ι → PrimeIdeal) : Finset PrimeIdeal :=
  Finset.univ.image p

lemma actualSupplyingLabels_norm_le (p : ι → PrimeIdeal) :
    (Ideal.absNorm (∏ P ∈ actualSupplyingLabels p,P.val) : ℝ) ≤
      ∏ i,(Ideal.absNorm (p i).val : ℝ) := by
  have h : (∏ P ∈ Finset.univ.image p,Ideal.absNorm P.val) ≤
      ∏ i,Ideal.absNorm (p i).val :=
    Finset.prod_image_le_of_one_le (fun P _ => Nat.one_le_iff_ne_zero.mpr
      (fun he => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp he)))
  simpa only [actualSupplyingLabels,map_prod,Nat.cast_prod] using
    (show ((∏ P ∈ Finset.univ.image p,Ideal.absNorm P.val) : ℝ) ≤
      ((∏ i,Ideal.absNorm (p i).val) : ℝ) by exact_mod_cast h)

/-- Actual annular upper support pays the supplying-prime radical. This uses
only the fixed finite slot count and the original individual length labels;
no assumption of distinct supplying primes or a squarefree norm is needed. -/
theorem actualSupplyingLabels_polynomial_cap (p : ι → PrimeIdeal) (length : ι → ℝ)
    (U : ℝ) (hU : 1 ≤ U) (hlarge : (2 : ℝ)^Fintype.card ι ≤ U)
    (hsupport : ∀ i,(Ideal.absNorm (p i).val : ℝ) ≤ 2*U^(length i)) :
    (Ideal.absNorm (∏ P ∈ actualSupplyingLabels p,P.val) : ℝ) ≤ U^(1+∑ i,length i) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  apply (actualSupplyingLabels_norm_le p).trans
  calc
    _ ≤ ∏ i,2*U^(length i) := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hsupport i)
    _ = (2 : ℝ)^Fintype.card ι*U^(∑ i,length i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←Real.rpow_sum_of_pos hUpos]
    _ ≤ U*U^(∑ i,length i) := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hUpos.le _)
    _ = _ := by rw [Real.rpow_add hUpos,Real.rpow_one]

#print axioms actualSupplyingLabels_polynomial_cap
end
end QRH.Cycle092.SignedCenter
