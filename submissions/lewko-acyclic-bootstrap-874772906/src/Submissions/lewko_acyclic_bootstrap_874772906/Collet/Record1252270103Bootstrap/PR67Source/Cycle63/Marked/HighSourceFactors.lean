import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionAnnular
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.BufferedRetainedRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighSourceEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Families
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open LowBranch CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable {P : HighSourceParameters} {η₀ : Character} {Z : ℝ}
variable {Dict : Type*} [Fintype Dict]

def HighSourceDatum.slotAmplitude (D : HighSourceDatum M H P η₀ Z Dict) (k : D.Slot) : ℂ :=
  naturalSlot (excluded D.natural.character D.state.puncture)
    (primePool M H P.B₀ (Z^(D.w k)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (D.θ k)) I*
      annularWeight P.Wslot (Z^(D.w k)) (D.σ k) (D.v k) I) D.t) (Z^(D.w k))

/-- The genuine buffered plain estimate leaves every surviving prime slot
in its literal form. This is the factorization used by joint density counting. -/
theorem actual_high_source_factored (P : HighSourceParameters) :
    ∃ n : ℕ,∃ Cp : ℝ,0<Cp ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀η₀ : Character,∀a : ℝ,51/100≤a→a≤1→∀i : ℕ,
      ∀{Dict : Type*} [Fintype Dict] (D : HighSourceDatum M H P η₀ Z Dict),
      HighSourceAdmissible hH P η₀ Z a i n D→
      ‖D.row P‖^2≤Cp^2*Z^((2*a-1)*
        (D.total P-∑k∈liveIndices D.projector D.allocation,D.w k)+2*P.εplain*P.d)*
          ∏k∈liveIndices D.projector D.allocation,‖D.slotAmplitude hH k‖^2 := by
  obtain ⟨n,Cp,hCp,hplain⟩:=actual_buffered_retained_plain_factors
    P.Rplain P.dmax P.τ P.εplain P.e P.κ P.vplain P.hRp P.hdmax P.hτ P.hεp
    P.he P.he' P.hκ P.hκ' P.hvp P.hplainBudget P.profileBound P.hprofile
  have hT : ∀ᶠZ : ℝ in atTop,2<Z^P.τ:=
    (tendsto_rpow_atTop P.hτ).eventually (eventually_gt_atTop _)
  refine ⟨n,Cp,hCp,?_⟩
  filter_upwards [hT,eventually_gt_atTop (1:ℝ)] with Z hZT hZ
  refine ⟨hZ,?_⟩
  intro η₀ a ha ha' i Dict _ D hD
  have hZp : 0<Z:=zero_lt_one.trans hZ
  have hcoeff (I : Ideal O) :
      idealCoeff D.state.character I*CanonicalRowCompletion.idealRowHom
        (D.state.mask^6*(1*D.z)) I=
      if false then star (idealCoeff (D.character D.member) I)
        else idealCoeff (D.character D.member) I := by
    simp only [Bool.false_eq_true,ite_false,hD.member,one_mul]
    simpa only [NaturalState.mask] using
      (D.natural.masked_ideal D.state.puncture D.state.puncture_ne_zero I).symm
  have hb:=hplain Z P.d hZ.le P.hd.le P.hdm hZT D.character D.hcharacter a i
    ha ha' hD.upper D.member D.state.character D.state.mask D.z false hcoeff
    (fun k : liveIndices D.projector D.allocation=>primePool M H P.B₀ (Z^(D.w k)))
    (fun k : liveIndices D.projector D.allocation=>fun I=>
      idealCoeff (relativeCharacter M H hH η₀ (D.θ k)) I*
        annularWeight P.Wslot (Z^(D.w k)) (D.σ k) (D.v k) I)
    (fun k : liveIndices D.projector D.allocation=>Z^(D.w k))
    (fun _=>Real.rpow_pos_of_pos hZp _) D.W D.X D.r D.A D.B D.t
    hD.X_pos hD.clipped_scale hD.A_pos
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.support)
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.smooth)
    hD.modulus hD.r_nonneg hD.r_bound hD.plain_frequency hD.plain_height
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.mellin₂)
    (by simpa only [orientedProfile,Bool.false_eq_true,ite_false] using hD.mellin_n)
  have hrow:=final_source_row_eq D.state D.source D.second D.projector D.allocation
    (fun k=>primePool M H P.B₀ (Z^(D.w k)))
    (fun k I=>idealCoeff (relativeCharacter M H hH η₀ (D.θ k)) I*
      annularWeight P.Wslot (Z^(D.w k)) (D.σ k) (D.v k) I)
    (fun k=>Z^(D.w k)) D.t D.z hD.character hD.mask hD.A hD.height
    hD.pool hD.coefficient hD.scale
  rw [hD.W₁,hD.W₂,hD.post_scale 0,hD.post_scale 1] at hrow
  have hpreX : ∀j,0<Cycle63.Physical.sourcePlainScales D.source.toSource D.second j := by
    intro j
    cases D.second <;> fin_cases j
    · exact D.source.X₁_pos
    · exact D.source.X₂_pos
    · exact D.source.Y₁_pos
    · exact D.source.Y₂_pos
  have he:=actual_high_allocation_exponent Z hZ D.projector D.allocation
    (Cycle63.Physical.sourcePlainScales D.source.toSource D.second) hpreX D.w P.d D.r
    (fun j=>by rw [hD.post_scale j];exact hD.clipped_scale j)
  rw [←funext hD.scale] at he
  change P.d*(D.r 0+D.r 1)+(∑k∈liveIndices D.projector D.allocation,D.w k)=D.total P at he
  have hexp : P.d*((2*a-1)*(D.r 0+D.r 1)+2*P.εplain)=
      (2*a-1)*(D.total P-∑k∈liveIndices D.projector D.allocation,D.w k)+2*P.εplain*P.d := by
    rw [←he]
    ring
  change ‖Cycle63.Physical.sourcePositiveRow D.source.toSource D.second
    D.projector D.allocation D.z‖^2≤_
  rw [hrow]
  apply hb.trans_eq
  rw [←Real.rpow_mul hZp.le,hexp]
  congr 1
  calc
    _ = ∏k : liveIndices D.projector D.allocation,‖D.slotAmplitude hH k.val‖^2 := by
      refine Finset.prod_congr rfl fun k hk => ?_
      congr 2
      exact (Deletion26.masked_natural_slot_eq D.natural D.state.puncture
        D.state.puncture_ne_zero _ _ _ _).symm
    _ = _ := Finset.prod_coe_sort (liveIndices D.projector D.allocation)
      (fun k : D.Slot=>‖D.slotAmplitude hH k‖^2)

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
