import Candidate.Cycle62.Moment.HighRawExponent

namespace OAI.SevenEighths.Cycle62ResidualReserve
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open Cycle62Moment Cycle62.Physical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem residual_slot_width_split (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (w : ι → ℝ) :
    (∑i∈frozenIndices D a,w i)+(∑i∈liveIndices D a,w i)=∑i,w i := by
  exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem selectedNorm_ge_one (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : 1 ≤ selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ) ≤ (selectedPlain D a j).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold selectedNorm
  nlinarith [hn 0, hn 1, mul_nonneg (sub_nonneg.mpr (hn 0)) (sub_nonneg.mpr (hn 1))]

theorem frozen_width_le_reduction (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (w : ι → ℝ) :
    (∑i∈frozenIndices D a,w i) ≤
      Real.logb Z (formalReductionFactor D a (fun i => Z^(w i))) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hs := Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  unfold formalReductionFactor
  rw [Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos hz _)).ne',
    Real.logb_prod _ _ (fun i _ => (Real.rpow_pos_of_pos hz (w i)).ne')]
  simp_rw [Real.logb_rpow hz hZ.ne']
  linarith

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {P : HighSourceParameters} {η₀ : Character} {Z : ℝ}
variable {Dict : Type*} [Fintype Dict]

/-- Residual frozen slots pay their full zero exponent even after the actual
clipping normalizer has been removed. This loss can pay a missing marked slot. -/
theorem high_source_exponent_frozen_saving
    (D : HighSourceDatum M H P η₀ Z Dict) (hZ : 1 < Z)
    (hscale : ∀i,D.source.P i=Z^(D.w i))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    δ*D.total P-sourcePostClip D.source.toSource D.second Z D.projector D.allocation ≤
      δ*Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume D.source)-
        δ*(∑i∈frozenIndices D.projector D.allocation,D.w i) := by
  have hr := frozen_width_le_reduction Z hZ D.projector D.allocation D.w
  rw [←funext hscale] at hr
  have hc : 0≤sourcePostClip D.source.toSource D.second Z D.projector D.allocation := by
    unfold sourcePostClip negativeTotal
    exact Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  rw [high_source_total_raw D hZ hscale]
  nlinarith [mul_le_mul_of_nonneg_left hr hδ,
    mul_nonneg (sub_nonneg.mpr hδ') hc]

end
end OAI.SevenEighths.Cycle62ResidualReserve
#print axioms OAI.SevenEighths.Cycle62ResidualReserve.frozen_width_le_reduction
#print axioms OAI.SevenEighths.Cycle62ResidualReserve.high_source_exponent_frozen_saving

#print axioms OAI.SevenEighths.Cycle62ResidualReserve.residual_slot_width_split
