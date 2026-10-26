import Candidate.Cycle63.Marked.HighSourceFactors
import Candidate.Cycle63.Marked.ResidualReserve
import Candidate.Cycle63.Physical.HighResidualAllocation

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedChildCapacity Cycle63.Physical Cycle63HighResidual
open Cycle63ResidualReserve
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable {P : HighSourceParameters} {η₀ : Character} {Z : ℝ}
variable {Dict : Type*} [Fintype Dict]

def HighSourceDatum.fullSlotWeight (D : HighSourceDatum M H P η₀ Z Dict) : ℝ :=
  ∏k,(max 1 ‖D.slotAmplitude hH k‖)^2

theorem HighSourceDatum.fullSlotWeight_nonneg (D : HighSourceDatum M H P η₀ Z Dict) :
    0≤D.fullSlotWeight hH := Finset.prod_nonneg (fun _ _=>sq_nonneg _)

theorem HighSourceDatum.live_product_le_full (D : HighSourceDatum M H P η₀ Z Dict) :
    (∏k∈liveIndices D.projector D.allocation,‖D.slotAmplitude hH k‖^2)≤D.fullSlotWeight hH := by
  calc
    _≤∏k∈liveIndices D.projector D.allocation,(max 1 ‖D.slotAmplitude hH k‖)^2:=by
      apply Finset.prod_le_prod₀ (fun _ _=>sq_nonneg _)
      intro k hk
      exact pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
    _≤_:=Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun _ _=>sq_nonneg _) (fun _ _ _=>one_le_pow₀ (le_max_left _ _))

/-- Residual frozen widths cancel the corresponding missing factors in
the high exponent. Enlarging the live product to all slots with `max 1`
then gives a bound independent of the residual allocation and rectangle. -/
theorem high_source_full_slot_envelope (D : HighSourceDatum M H P η₀ Z Dict)
    (hZ : 1<Z) (hscale : ∀k,D.source.P k=Z^(D.w k))
    (δ C error : ℝ) (hδ : 0≤δ) (hδ' : δ≤1) (hC : 0≤C)
    (hrow : ‖D.row P‖^2≤C*Z^(δ*(D.total P-
      ∑k∈liveIndices D.projector D.allocation,D.w k)+error)*
        ∏k∈liveIndices D.projector D.allocation,‖D.slotAmplitude hH k‖^2) :
    (normalizedPositiveNorm D.source.toSource D.second Z D.projector D.allocation D.z)^2≤
      C*Z^(δ*(Real.logb Z (preVolume D.source)-∑k,D.w k)+error)*D.fullSlotWeight hH := by
  have hZp : 0<Z:=zero_lt_one.trans hZ
  have hf:=high_source_exponent_frozen_saving D hZ hscale δ hδ hδ'
  have hs:=residual_slot_width_split D.projector D.allocation D.w
  have he : δ*(D.total P-∑k∈liveIndices D.projector D.allocation,D.w k)+error-
      sourcePostClip D.source.toSource D.second Z D.projector D.allocation≤
      δ*(Real.logb Z (preVolume D.source)-∑k,D.w k)+error := by
    rw [←hs]
    nlinarith
  have hb:=normalizedPositiveNorm_sq_bound D.source.toSource D.second Z hZp
    D.projector D.allocation D.z
    (C*(∏k∈liveIndices D.projector D.allocation,‖D.slotAmplitude hH k‖^2))
    (δ*(D.total P-∑k∈liveIndices D.projector D.allocation,D.w k)+error)
    (hrow.trans_eq (by ring))
  apply hb.trans
  calc
    _≤(C*D.fullSlotWeight hH)*Z^(δ*(Real.logb Z (preVolume D.source)-∑k,D.w k)+error) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (D.live_product_le_full hH) hC
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le he
      · exact Real.rpow_nonneg hZp.le _
      · exact mul_nonneg hC (D.fullSlotWeight_nonneg hH)
    _=_:=by ring

theorem high_source_row_full_slot_envelope (D : HighSourceDatum M H P η₀ Z Dict)
    (hZ : 1<Z) (hscale : ∀k,D.source.P k=Z^(D.w k))
    (δ C error : ℝ) (hδ : 0≤δ) (hδ' : δ≤1) (hC : 0≤C)
    (hrow : ‖D.row P‖^2≤C*Z^(δ*(D.total P-
      ∑k∈liveIndices D.projector D.allocation,D.w k)+error)*
        ∏k∈liveIndices D.projector D.allocation,‖D.slotAmplitude hH k‖^2) :
    ‖D.row P‖^2≤(C*D.fullSlotWeight hH)*
      Z^(δ*(Real.logb Z (preVolume D.source)-∑k,D.w k)+error+
        sourcePostClip D.source.toSource D.second Z D.projector D.allocation) := by
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hh:=high_source_full_slot_envelope hH D hZ hscale δ C error hδ hδ' hC hrow
  rw [normalizedPositiveNorm_sq _ _ Z hz] at hh
  have he:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp hh
  apply he.trans_eq
  rw [Real.rpow_add hz (δ*(Real.logb Z (preVolume D.source)-∑k,D.w k)+error)
    (sourcePostClip D.source.toSource D.second Z D.projector D.allocation)]
  ring

end
end OAI.SevenEighths.Cycle63Moment
