import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildDaughter
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildProfiles
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildEnergyClip
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowUniform
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildRetainedCapacity
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildNonunitWidth
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildTotalLength
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildPrimeReserve
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Dispatch
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.SecondApplicable
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.SecondStepOfChild
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.DirectBranchFacts
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBridge
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelCertificates
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBranches
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.SdiffSum
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The bound of one final daughter of a first-level LOW child with the second step, for the original plain profiles: the
old moment at the width of the child, the allowance of its labels and the count form of the HIGH part of the second
step. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCompleteCommon CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentRankinRadical CenteredMomentPartitionNorm CenteredMomentFirstMixedRoot
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondMovingSupport CenteredMomentSupport
open CenteredMomentFirstCanonicalFamily
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity CenteredMomentEnergyInputParentCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The log norms of the ideals of a live LOW child: its own first ideal, the other one, its own second ideal and the
inactive set are nonnegative; the inactive set is below the common frequency generator, which exceeds the own second
ideal by at most the inactive set; the active conductor is below the other first ideal and the common radical below the
own second ideal. -/
theorem live_child_log_facts {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hZ : 1 < Z) :
    0 ≤ Real.logb Z (q.C₁.absNorm : ℝ) ∧ 0 ≤ Real.logb Z (g.D₁.absNorm : ℝ) ∧
    0 ≤ Real.logb Z (q.E₂.absNorm : ℝ) ∧
    0 ≤ Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ∧
    Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ≤
      Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)) ∧
    Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)) -
      Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ≤ Real.logb Z (q.E₂.absNorm : ℝ) ∧
    Real.logb Z (normValue (activeConductor q.C₁ g.D₁)) ≤ Real.logb Z (g.D₁.absNorm : ℝ) ∧
    Real.logb Z ((commonRadical g.datum.C g.datum.D).absNorm : ℝ) ≤ Real.logb Z (q.E₂.absNorm : ℝ) := by
  have nn : ∀ I : Ideal O, Supported I → 0 ≤ Real.logb Z (I.absNorm : ℝ) := fun I hI =>
    Real.logb_nonneg hZ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1))
  have hE : Supported q.E₂ := by
    rcases g.label with h | h
    · rw [h]; exact g.datum.hC
    · rw [h]; exact g.datum.hD
  have hU : (∏ p ∈ g.datum.inactive, p.val) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (commonPrime_supported_ideal _ _ g.datum.hC p).1)
  refine ⟨nn _ g.hC₁, nn _ g.hD₁, nn _ hE, ?_,
    CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.datum.C g.datum.D g.datum.hC g.datum.inactive Z hZ,
    ?_, logb_activeConductor_le_right q.C₁ g.D₁ g.hC₁ g.hD₁ Z hZ,
    logb_commonRadical_le g.datum.C g.datum.D q.E₂ g.datum.hC g.datum.hD g.datum.sameSupport g.label Z hZ⟩
  · exact Real.logb_nonneg hZ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU))
  · rcases g.label with h | h
    · rw [h]; exact actual_common_shift_le g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport
        g.datum.inactive Z hZ
    · rw [h]; exact actual_common_shift_le_right g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport
        g.datum.inactive Z hZ

/-- A bound with two exponents that agree has the same right side. -/
theorem rpow_add_congr {Z E₁ E₂ Ret C : ℝ} (h : E₁ = E₂) : C * (Z ^ E₁ + Ret) = C * (Z ^ E₂ + Ret) := by
  rw [h]

/-- The bound of one final daughter of a first-level LOW child with the second step, for the original plain profiles
`p₀` of the class `(a, b)`. A final daughter is either in the old region after the fixed deletion (branch O), or
reflected into it (R), or wide enough for the second step (L2), or narrow, and then deleted directly into the old region
(D). The bound is `LowProfilesStmt` for the units `unit = 1`, the frequency losses at most `ωmax`, the rate
`q/(6 slotPrice)` of the padding, the reflection loss `εR`, the allowance `lowAllowance` of the labels and the returned
part of the second step. The ledger is the first step of the two-level ledger (`IsTwoLevelFirstStep`); the numeric
facts are in `TwoLevelCertificates`; the second step is `stepTwo`, at the class `(a, b)`. The grid of the second step
has mesh `1/G`; the cap of the plain scales is at least one (`1 ≤ L`), because the widened state of a child has width
at most one. The split and the second step run with the profiles `p₀` and the literal plain scales `profileScales` of
the final daughter, which are not clipped. The lengths of the literal and of the clipped scales agree
(`length_clippedScale`), so the facts of the first level apply unchanged; and the energy of the final daughter, at the
clipped scales and with the profiles dilated by the clipping factors, is at most the energy at the literal scales
(`energy_clipped_le`). The slots have length at most the slot bound `Lslot`, a parameter of the second step below the
common mesh of the old moment (`hLslot`). -/
theorem two_level_low_profiles [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger] {Base : Type}
    (W : ℝ→ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<a) (hap' : a≤1/4) (hbp : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hLslot : Lslot≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (G : ℕ) (ωmax ξR δR εR lossFloor gridSlack ampSlack Bnorm : ℝ)
    (hξR : 0<ξR) (hδR : 0≤δR) (hεR : 0<εR) (hL1 : 1≤L)
    (hcert : TwoLevelCertificates G Mcap εpad ωmax ξR δR gridSlack ampSlack)
    (base : Character → Base → Character)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (stepTwo : SecondStepReturnAt (α:=α) M H hH base W B a b 2 Bmask L Lslot lo hi Mcap εold Bnorm
      (SecondApplicable G lossFloor Presented)) :
    LowProfilesStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      (fun u om _ => u=1 ∧ om≤ωmax) True (Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)) εR
      (fun Z C₁ D₁ C₂ D₂ E₂ => lowAllowance Z C₁ D₁ C₂ D₂ E₂) base Bnorm lossFloor gridSlack ampSlack Presented := by
  have hq0 : 0 ≤ Cycle63.AffineLedger.q := Cycle63.AffineLedger.q_pos.le
  have hq1 : Cycle63.AffineLedger.q ≤ 1 := Cycle63.AffineLedger.q_le_one
  have hdisp := low_state_dispatch (α:=α) M H hH W A B a b 2 Bmask L Lslot lo hi Mcap εold
    hA hWs hW hB hap hap' hbp (by norm_num) hBmask hMcap hεold hLslot hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    Cycle63.AffineLedger.q hq0 hq1 ξR δR εR hξR hδR hεR base Bnorm (SecondApplicable G lossFloor Presented) stepTwo
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree,S,Kc,K,hK,hbound⟩ := hdisp η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,S,Kc,K,hK,?_⟩
  filter_upwards [hbound,Cycle63FinalRadius.fixed_final_width_constants_uniform
    (Fintype.card α) bs 1 (εwidth/2) Mmin (zero_lt_one.trans_le hbs) (by norm_num) (by positivity) hmin,
    support_padding_eventually_mass (Fintype.card α) bs b b εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hconstants hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh unit Mrow omega ξ hMmin hadm hω hξ hMcap' hfit hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p₀ hp₁ hp₂ hXcap₁ hXcap₂ v₁ Tz hpres
    hQM' hQη low
  obtain ⟨hunit1,hωmax⟩ := hadm
  subst hunit1
  -- the cell of the parent
  have hM : (0:ℝ) < 1 := one_pos
  obtain ⟨hc₁,hc₂,-,hc₄⟩ := Cycle63.AffineLedger.originalCell_mem
    (show Cycle63.AffineLedger.slotFloor ≤ (∑ j,Real.logb Z (s.P j))/1 ∧
        (∑ j,Real.logb Z (s.P j))/1 ≤ Cycle63.AffineLedger.slotTop from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle63.AffineLedger.cellUpper_bounds hc₁ hc₂
  have hbwin := cell_range hcell
  have hbwin' : Cycle63.Optimization.firstCellTop ≤ cell ∧ cell ≤ Cycle63.Optimization.slotTop := hbwin
  have hamp0 : 0 < Cycle63.AffineLedger.amp cell := Cycle63.AffineLedger.amp_pos hcell
  have hamp_eq : Cycle63.AffineLedger.amp cell = Cycle63.Optimization.firstAmp cell := amp_eq cell
  have hg_eq : Cycle63.AffineLedger.g cell = Cycle63.Optimization.twoLevelOldGap cell := g_eq cell
  have htot_eq : Cycle63.AffineLedger.totalA cell = Cycle63.Optimization.twoLevelTotalA cell := totalA_eq cell
  have hdel_eq : fixedDel cell = Cycle63.Optimization.fixedDeletion cell := fixedDel_eq cell
  have hamp' : amp = Cycle63.Optimization.firstAmp cell := by
    show 1*Cycle63.AffineLedger.amp cell = _
    rw [one_mul,hamp_eq]
  obtain ⟨hnc,hnd,hne,hnt,htg,hge,hRd,hradE⟩ := live_child_log_facts g hZone
  have hnominal : nominal ≤ 1 := by
    have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.datum.C g.datum.D g.datum.hC
      g.datum.inactive Z hZone
    have hnmax : 0 ≤ max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0 := le_max_right _ _
    have hamp : 0 ≤ amp := by
      show 0 ≤ 1*Cycle63.AffineLedger.amp cell
      linarith only [hamp0]
    unfold nominal secondNominal
    linarith only [hshift,hnmax,hamp,hω]
  have hwidth : st.width-nominal ≤ δwidth :=
    live_main_state_width_unit g Bmask hZone (zero_lt_one.trans_le hbs) χ (internalQ Q η₀) hP hPN hfit
      (hconstants.2 1 hMmin)
  have hδ : 0 ≤ δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0 ≤ padding := by dsimp [padding]; positivity
  have hs : st.width ≤ Mcap := by dsimp only [δwidth] at hwidth; linarith only [hwidth,hnominal,hMcap']
  by_cases live : ∃ z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    have hP1 : ∀ j,1 ≤ s.P j := fun j => by
      rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)
    -- the literal plain scales of the final daughter are at most the clipped ones and have the same lengths
    have hlen₀ : length Z (profileScales src second L₂ alloc 0) = length Z (finalPlain src second L₂ alloc 0) := by
      unfold finalPlain
      exact (length_clippedScale Z _).symm
    have hlen₁ : length Z (profileScales src second L₂ alloc 1) = length Z (finalPlain src second L₂ alloc 1) := by
      unfold finalPlain
      exact (length_clippedScale Z _).symm
    have hUle₀ : profileScales src second L₂ alloc 0 ≤ finalPlain src second L₂ alloc 0 := by
      unfold finalPlain clippedScale profileScales
      exact le_max_right _ _
    have hUle₁ : profileScales src second L₂ alloc 1 ≤ finalPlain src second L₂ alloc 1 := by
      unfold finalPlain clippedScale profileScales
      exact le_max_right _ _
    -- the capacities of the child
    have htotal : length Z (profileScales src second L₂ alloc 0)+length Z (profileScales src second L₂ alloc 1)+
        (6*Cycle63.Optimization.slotPrice)*(∑ j ∈ q.indices L₂ alloc,w j)-nominal ≤
        1*Cycle63.AffineLedger.g cell+6*amp+omega+supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-
          (min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
            (Real.logb Z (q.E₂.absNorm:ℝ)-(Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
              Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ)))) := by
      have h := live_main_source_capacity_retained g hbs hsupper hZone hM hP1 hz haff (g.datum.τ χ) v second L₂
        alloc z hzrow
      rw [original_slot_sum s q (g.datum.τ χ) v Z hZone w hm.scale L₂ alloc] at h
      rw [hlen₀, hlen₁]
      exact h
    have htotalu : length Z (profileScales src second L₂ alloc 0)+length Z (profileScales src second L₂ alloc 1)+
        (∑ j ∈ q.indices L₂ alloc,w j) ≤
        Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z := by
      have h := live_main_total_length g hbs hsupper hZone hP1 (g.datum.τ χ) v second L₂ alloc z hzrow
      rw [original_slot_sum s q (g.datum.τ χ) v Z hZone w hm.scale L₂ alloc] at h
      rw [hlen₀, hlen₁]
      exact h
    have hpadd : supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z ≤ εpad*1 := by
      rw [hsb₁,hsb₂]
      exact hpadLoss.2 1 hMmin
    have hspad0 : 0 ≤ supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z := by
      unfold supportPadding
      have h1 : 0 ≤ Real.logb Z bs := Real.logb_nonneg hZone hbs
      have h2 : 0 ≤ Real.logb Z (max 1 s.b₁*max 1 s.b₂) :=
        Real.logb_nonneg hZone (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
      have h3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg (Fintype.card α))) h1
      linarith only [h2,h3]
    have hremle : (∑ j ∈ q.indices L₂ alloc,w j) ≤ cell := by
      have h1 : (∑ j ∈ q.indices L₂ alloc,w j) ≤ ∑ j,w j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hw j)
      have h2 : (∑ j,Real.logb Z (s.P j)) = ∑ j,w j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hm.scale j,Real.logb_rpow (zero_lt_one.trans hZone) hZone.ne']
      have h3 : (∑ j,Real.logb Z (s.P j))/1 ≤ cell := hc₄
      linarith only [h1,h2,h3]
    have hvol : Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA cell := by
      obtain ⟨-,-,-,htot4,-⟩ := Cycle63.AffineLedger.normalized_cell_bounds hM hz haff
      rw [input_volume_log]
      have h1 := raw_log_le_length Z s.X₁ hZone s.X₁_pos
      have h2 := raw_log_le_length Z s.X₂ hZone s.X₂_pos
      simp only [one_mul] at htot4
      linarith only [h1,h2,htot4]
    have hnonunit : Real.logb Z (normValue (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive))+
        Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ) ≤ nominal+δwidth := by
      have hc := hconstants.2 1 hMmin
      rw [Real.logb_one] at hc
      exact live_main_nonunit_width g hZone (zero_lt_one.trans_le hbs) hfit (by linarith only [hc])
    obtain ⟨hrate0,hrate2⟩ := directDeletionRate_bounds
    have hrate : Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice) =
        Cycle63.Optimization.directDeletionRate := directRate_eq
    have hne : idealCorrelation g.datum.C g.datum.D g.datum.hC g.datum.hD
        (commonFrequencyGenerator g.datum.C g.datum.D*
          (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive*g.row.val.2.2.2.val)) ≠ 0 := by
      simpa only [SecondInputDatum.block,originalSecondBlock,SecondBlockSource.frequency,mul_assoc]
        using actual_second_live_correlation (fun _ : Unit => g.datum.block) g.row
    have hprime := second_pair_prime_reserve g.datum.C g.datum.D q.E₂ g.datum.hC g.datum.hD g.datum.sameSupport
      g.label g.datum.inactive _ hne Z hZone (κq:=Cycle63.Optimization.directDeletionRate) hrate0 hrate2
    -- the facts in terms of the two-level layer
    have hνdef : nominal = 1-(max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0+
        Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
        Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ))-6*Cycle63.Optimization.firstAmp cell-omega := by
      unfold nominal secondNominal
      linarith only [hamp']
    have hLr : Cycle63.Optimization.lowReserveAt Cycle63.Optimization.twoLevelPrice
        Cycle63.Optimization.twoLevelIntercept Cycle63.Optimization.firstJunction ≤
        Cycle63.Optimization.firstAmp cell := by
      have h := lowReserve_le_amp hcell
      rw [lowReserve_eq,hamp_eq] at h
      exact h
    have hN4' : length Z (profileScales src second L₂ alloc 0)+length Z (profileScales src second L₂ alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑ j ∈ q.indices L₂ alloc,w j)-nominal ≤
        Cycle63.Optimization.twoLevelOldGap cell+6*Cycle63.Optimization.firstAmp cell+omega+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-
          (min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
            ((Real.logb Z (q.E₂.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)))+
              Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ))) := by
      have h := htotal
      rw [hg_eq] at h
      linarith only [h,hamp']
    have hA : Real.logb Z (volume s) ≤ Cycle63.Optimization.twoLevelTotalA cell := by
      rw [←htot_eq]; exact hvol
    have hspad : supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z ≤ εpad := by linarith only [hpadd]
    have hδmax : δwidth ≤ Mcap-1 := by dsimp only [δwidth]; linarith only [hMcap']
    have hmt : 0 ≤ (Cycle63.Optimization.twoLevelSlope-1)*Cycle63.Optimization.cellMesh := by
      have h1 : 1 ≤ Cycle63.AffineLedger.lam := Cycle63.AffineLedger.one_le_lam
      have h2 : 0 < Cycle63.AffineLedger.cellMesh := Cycle63.AffineLedger.cellMesh_pos
      rw [IsTwoLevelFirstStep.lam_eq] at h1
      rw [IsTwoLevelFirstStep.cellMesh_eq] at h2
      exact mul_nonneg (by linarith only [h1]) h2.le
    have hfirst : Cycle63.Optimization.firstAmp Cycle63.Optimization.firstCellTop ≤
        Cycle63.Optimization.firstAmp cell := firstAmp_mono hcell
    have hdel0 : 0 ≤ 1*Cycle63.Optimization.fixedDeletion cell := by
      rw [one_mul,←hdel_eq]; exact fixedDel_nonneg hcell
    have hX0 : 0 ≤ lowAllowance Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂ :=
      lowAllowance_nonneg hZone _ _ _ _ _ g.datum.hC g.datum.hD g.datum.sameSupport g.label
    have hqdel : Cycle63.AffineLedger.q*(1*Cycle63.Optimization.fixedDeletion cell) ≤
        amp-1*Cycle63.AffineLedger.lowReserve := by
      have h := fixedDel_pays cell
      rw [hdel_eq] at h
      have hamp'' : amp = Cycle63.AffineLedger.amp cell := one_mul _
      linarith only [h,hamp'']
    have hWMcap : nominal+δwidth ≤ Mcap := by dsimp only [δwidth]; linarith only [hnominal,hMcap']
    -- the widened state of the child has width at most one: the widths of the cell leave the room `Mcap - 1`
    have hWu : nominal+δwidth ≤ 1 := by
      have hv0 : 0 ≤ max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0+
          Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
          Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ) := by
        linarith only [le_max_right (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0,htg]
      have h6 := hcert.width
      linarith only [hνdef,hv0,hfirst,hδmax,hω,h6]
    have hWL : nominal+δwidth ≤ L := hWu.trans hL1
    have hRR : Real.logb Z (((Ideal.span {activeConductor q.C₁ g.D₁}).absNorm:ℕ):ℝ) =
        Real.logb Z (normValue (activeConductor q.C₁ g.D₁)) := rfl
    obtain ⟨Ret,hRet0,hRetcl,henergy⟩ := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh aLow i hw hwL
      (fun j _ => hwr j) hmesh (fun j _ => hwm j) hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh st rfl hs p₀
      (profileScales src second L₂ alloc 0) (profileScales src second L₂ alloc 1)
      (profile_scales_pos src second L₂ alloc 0) (profile_scales_pos src second L₂ alloc 1)
      (hUle₀.trans hXcap₁) (hUle₁.trans hXcap₂)
      nominal δwidth padding amp (1*Cycle63.AffineLedger.lowReserve) (1*Cycle63.Optimization.fixedDeletion cell)
      (lowAllowance Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)
      (max (Cycle63.Optimization.twoLevelOldGap cell+6*Cycle63.Optimization.firstAmp cell-
        (min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
          ((Real.logb Z (q.E₂.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)))+
            Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ)))) 0)
      (Cycle63.Optimization.secondStepWidthFloor ≤ nominal+δwidth) v₁ Tz (nominal+δwidth)
      (length Z (profileScales src second L₂ alloc 0)+length Z (profileScales src second L₂ alloc 1)+
        ((∑ j ∈ q.indices L₂ alloc,w j)-Cycle63.Optimization.fixedDeletion cell)+
          Cycle63.Optimization.secondSlope/G)
      (Cycle63.Optimization.secondAmp cell+
          Cycle63.Optimization.amplifierRatio Cycle63.Optimization.slotPrice 1 Cycle63.Optimization.secondJunction*
          ((omega+supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z)+omega)+
        Cycle63.Optimization.amplifierRatio Cycle63.Optimization.slotPrice 1 Cycle63.Optimization.secondJunction*
          (1+6*Cycle63.Optimization.slotPrice)/G)
      lossFloor hwidth hδ hpadding hdel0 hX0 hqdel hWMcap hWL
      (by
        intro hnw
        have hnarrow : nominal+δwidth < Cycle63.Optimization.secondStepWidthFloor := not_le.mp hnw
        obtain ⟨h1,h2,h3⟩ := two_level_branch_D (b:=cell) hcert hbwin' hnc hnd hnt hRd hradE hep.le hspad hω hωmax
          hδ hδmax hνdef hnonunit hprime hN4' hLr hnarrow
        refine ⟨h1,?_,?_⟩
        · dsimp only [padding]; linarith only [h2]
        · rw [hrate]
          unfold lowAllowance lowSurplus
          rw [hRR,lowReserve_eq]
          linarith only [h3,hamp'])
      (by
        intro hwd hsW R hRJ hRne hsum hdR hnotO hnotR
        refine And.intro ?_ (hpres _ hsW)
        rw [widenState_width]
        obtain ⟨hzeq,hz'0⟩ := sum_sdiff_eq_sub (q.indices L₂ alloc) R w hw hRJ
        refine two_level_branch_L2 (b:=cell) (dl:=∑ j ∈ R,w j) hcert hbwin' hξR hnc hnd htg hge hspad0 hspad hω
          hωmax hδ hδmax hmt hνdef hN4' htotalu hA hremle hwd hfirst (by linarith only [hdR]) hzeq.symm
          hz'0 ?_ ?_
        · intro h; apply hnotO; unfold OldRegionTest; rw [hzeq]; exact h
        · intro h; apply hnotR; unfold ReflectionTest; rw [hzeq]; exact h)
    refine ⟨Ret,hRet0,?_,?_⟩
    · rcases hRetcl with h0 | ⟨unit₂,Hb,hpays,hcls,hReteq⟩
      · exact Or.inl h0
      · refine Or.inr ⟨trivial,⟨unit₂,Hb,st.rowWidth,_,_,lossFloor,hpays⟩,rfl,rfl,?_,?_,hcls,hReteq⟩
        · have h := hcert.length
          show _ ≤ _
          linarith only [h,htotalu]
        · have h := two_level_amp_le (b:=cell) hcert hspad hωmax
          show _ ≤ _
          linarith only [h]
    · rw [original_low_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.datum.τ χ) v (internalQ Q η₀) hP hPN
        g.datum.radius g.datum.C g.datum.D g.datum.inactive second L₂ alloc _,hp₁,hp₂]
      refine energy_clipped_le_of_le _ _ _ _ _ _ _ _ _ (fun j => Real.rpow_pos_of_pos (zero_lt_one.trans hZone) _)
        _ _ (profile_scales_pos src second L₂ alloc 0) (profile_scales_pos src second L₂ alloc 1) _ _ _ _
        (natural_energy_nonneg st _ _ _ _ _ _ _ _ _) ?_
      refine henergy.trans_eq ?_
      exact rpow_add_congr (by ring)
  · have hzrow : ∀ z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    refine ⟨0,le_rfl,Or.inl rfl,?_⟩
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    have hZE : 0 ≤ Z^(nominal+δwidth+amp-1*Cycle63.AffineLedger.lowReserve+εold+εR+2*ε*d*(Fintype.card α:ℝ)+
      Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*padding+Cycle63.AffineLedger.q*mesh+
      lowAllowance Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂) := Real.rpow_nonneg (zero_le_one.trans hZone.le) _
    positivity

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
