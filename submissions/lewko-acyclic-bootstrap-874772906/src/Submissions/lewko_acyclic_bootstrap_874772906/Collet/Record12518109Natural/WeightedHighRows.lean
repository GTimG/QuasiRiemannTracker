/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Adapted from Cycle61.Moment.{HighRetainedRows,HighSourceRows,HighSourceEnergy}
and their OpenAI/math buffered plain and retained-energy interfaces
(Apache-2.0). The literal slot product is retained for the gain supplier. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.HighSourceEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.HighRawExponent

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61Moment
local notation "O" => HeckeFamily.O

/-- This is the literal physical normalized-slot weight before residual
allocation. Maximum with one permits all subsequent slot deletions. -/
def sourceSlotMaximum {ι : Type} [Fintype ι] (s : Data ι) (z : O) : ℝ :=
  ∏ k, max 1 (‖normalizedSlot s.η s.m s.A z (s.slots k)
    (s.coefficient k) s.t (s.P k)‖^2)

theorem sourceSlotMaximum_nonneg {ι : Type} [Fintype ι] (s : Data ι) (z : O) :
    0 ≤ sourceSlotMaximum s z :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))

theorem live_slot_product_le_maximum {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (z : O) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (ι⊕Fin 2))) :
    (∏ k : liveIndices L alloc, ‖normalizedSlot s.η s.m s.A z
      (s.slots k) (s.coefficient k) s.t (s.P k)‖^2) ≤ sourceSlotMaximum s z := by
  rw [Finset.prod_coe_sort (liveIndices L alloc) (fun k : ι =>
    ‖normalizedSlot s.η s.m s.A z (s.slots k) (s.coefficient k) s.t (s.P k)‖^2)]
  apply (Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
    (fun _ _ => le_max_right _ _)).trans
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun _ _ => zero_le_one.trans (le_max_left _ _)) (fun _ _ _ => le_max_left _ _)

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine buffered plain estimates for the actual retained source row,
with every live slot left in its physical maximum weight. No marked moment
or energy estimate is an input to this theorem. -/
theorem actual_high_source_datum_weighted (P : HighSourceParameters) :
    ∃ n : ℕ, ∃ Cp : ℝ, 0 < Cp ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ η₀ : Character, ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 → ∀ i : ℕ,
      ∀ {Dict : Type*} [Fintype Dict] (D : HighSourceDatum M H P η₀ Z Dict),
      HighSourceAdmissible hH P η₀ Z a i n D →
        ‖D.row P‖^2 ≤ Cp^2*
          Z^((2*a-1)*(D.total P-(∑ k∈liveIndices D.projector D.allocation,D.w k))+
            2*P.εplain*P.d)*sourceSlotMaximum D.source D.z := by
  obtain ⟨n,Cp,hCp,hplain⟩ := actual_buffered_retained_plain_factors
    P.Rplain P.dmax P.τ P.εplain P.e P.κ P.vplain P.hRp P.hdmax P.hτ P.hεp
      P.he P.he' P.hκ P.hκ' P.hvp P.hplainBudget P.profileBound P.hprofile
  have hT : ∀ᶠ Z : ℝ in atTop, 2 < Z^P.τ :=
    (tendsto_rpow_atTop P.hτ).eventually (eventually_gt_atTop _)
  refine ⟨n,Cp,hCp,?_⟩
  filter_upwards [hT,eventually_gt_atTop (1:ℝ)] with Z hZT hZ
  refine ⟨hZ,?_⟩
  intro η₀ a ha ha' i Dict _ D hD
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hcoeff (I : Ideal O) :
      idealCoeff D.state.character I*CanonicalRowCompletion.idealRowHom (D.state.mask^6*(1*D.z)) I =
        if false then star (idealCoeff (D.character D.member) I) else idealCoeff (D.character D.member) I := by
    simp only [Bool.false_eq_true,ite_false,hD.member,one_mul]
    simpa only [NaturalState.mask] using
      (D.natural.masked_ideal D.state.puncture D.state.puncture_ne_zero I).symm
  have hp := hplain Z P.d hZ.le P.hd.le P.hdm hZT D.character D.hcharacter a i ha ha' hD.upper
    D.member D.state.character D.state.mask D.z false hcoeff
    (fun k : liveIndices D.projector D.allocation => D.source.slots k)
    (fun k : liveIndices D.projector D.allocation => D.source.coefficient k)
    (fun k : liveIndices D.projector D.allocation => D.source.P k)
    (fun k => D.source.P_pos k) D.W D.X D.r D.A D.B D.t hD.X_pos hD.clipped_scale hD.A_pos
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.support)
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.smooth)
    hD.modulus hD.r_nonneg hD.r_bound hD.plain_frequency hD.plain_height
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.mellin₂)
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.mellin_n)
  have hrow := final_source_row_eq D.state D.source D.second D.projector D.allocation
    D.source.slots D.source.coefficient D.source.P D.t D.z hD.character hD.mask hD.A hD.height
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  rw [hD.W₁,hD.W₂,hD.post_scale 0,hD.post_scale 1] at hrow
  have hpreX : ∀ j, 0 < Cycle61.Physical.sourcePlainScales D.source.toSource D.second j := by
    intro j
    cases hs : D.second <;> fin_cases j
    · exact D.source.X₁_pos
    · exact D.source.X₂_pos
    · exact D.source.Y₁_pos
    · exact D.source.Y₂_pos
  have he := actual_high_allocation_exponent Z hZ D.projector D.allocation
    (Cycle61.Physical.sourcePlainScales D.source.toSource D.second) hpreX D.w P.d D.r
    (fun j => by rw [hD.post_scale j]; exact hD.clipped_scale j)
  rw [←funext hD.scale] at he
  change P.d*(D.r 0+D.r 1)+(∑ k∈liveIndices D.projector D.allocation,D.w k)=D.total P at he
  have heq : P.d*((2*a-1)*(D.r 0+D.r 1)+2*P.εplain) =
      (2*a-1)*(D.total P-(∑ k∈liveIndices D.projector D.allocation,D.w k))+2*P.εplain*P.d := by
    rw [←he]; ring
  have hslots := live_slot_product_le_maximum D.source D.z D.projector D.allocation
  rw [HighSourceDatum.row,hrow]
  apply hp.trans
  rw [←Real.rpow_mul hZp.le,heq]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [hD.character,hD.mask,hD.A,hD.height] using hslots)
    (mul_nonneg (sq_nonneg Cp) (Real.rpow_nonneg hZp.le _))

end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.sourceSlotMaximum_nonneg
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.live_slot_product_le_maximum
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.actual_high_source_datum_weighted
