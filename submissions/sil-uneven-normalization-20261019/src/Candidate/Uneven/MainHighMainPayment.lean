/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainHighCoordinates
import Candidate.Target830.Marked.Schedule
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Uneven.MainHighMainProjectorPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCoarseFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryMainBufferedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryFiber
import Candidate.Cycle63.Physical.InitialMass.GeometryHighCoarseGates
import Candidate.Cycle63.Moment.HighParameters

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.MainHigh
open TargetHigh830 SaturatedPlain BootstrapPlain
open OAI.SevenEighths.Cycle63InitialMass
open Target830 Marked830Plain
noncomputable section
open Cycle63MarkedPlain
open scoped ContDiff
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
local instance geometryMainHighPaymentSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource


open Cycle63FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Literal original-nonzero physical second blocks supply the small norm
caps, retained puncture budget, actual unit profile, fixed width ceiling,
and one full buffered selector. The threshold precedes all block labels. -/
theorem eventually_actual_main_high_literal_admission
    {α : Type} [Fintype α] [DecidableEq α]
    (η : Character)(b bs loss ξ τ e Bmask bΦ : ℝ)
    (hb : 1 ≤ b)(hbs : 1 ≤ bs)(hloss : 0<loss)(hloss1 : loss ≤ 1)
    (hξ : 0 ≤ ξ)(hξ1 : ξ ≤ 1)(hτ : 0<τ)(he : 0<e)(hmask : 8 ≤ Bmask)(hbΦ : 2 ≤ bΦ)
    (η₀ : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(reflected second : Bool)(s : Input α)(_hη : s.η=η)
        (seed : Ideal O)(amp reserve t : ℝ),
      Endpoints b bs bs s → Squarefree seed →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      sourceRadius s ≤ Z^(3:ℝ) → volume s ≤ Z^(3:ℝ) → 0 ≤ amp → 0 ≤ reserve →
      |Real.logb Z (volume s)| ≤ 4 → |amp| ≤ 4 → |frequencyLoss Z 32 ξ+reserve| ≤ 4 →
      ∀(bin : ℤ×(Fin 5→ℤ))(χ₀ : RayCharacter)(Q₀ : Ideal O)
        (_hQ₀ : Q₀ ≤ Ideal.span {(72:O)})(m : O)(_hm : m≠0)
        (_hml : ConcretePrimeRowBridge.goodLambda∣m)(_hm2 : (2:O)∣m)
        (hQM : Q₀ ≤ M)(hQη : Q₀ ≤ η₀.modulus)
        (_hβlo : 51/100 ≤ HeckeZeroSupremum.beta)(_hβhi : HeckeZeroSupremum.beta ≤ 7/8)
        (j : geometryMainNonzeroBlocks reflected s 1 seed Z 1 amp ξ reserve b t
          (Fintype.card α) hZ bin hs₁ hs₂),
      let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
      let d:=geometryLowSecondDatum reflected s 1 seed Z 1 amp ξ reserve b t
        (Fintype.card α) hZ bin j.val.1 hs₁ hs₂ j.val.2
      let ordinary:=fun _:Unit=>ordinarySecondDatum d χ₀ Q₀ m
      let rows:=secondLiveRows (fun l=>(ordinary l).block)
      let l:=geometryFirstLabel s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val
      (l.1.1.absNorm:ℝ) ≤ Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ) ≤ Z^(4:ℝ) ∧
      (d.C.absNorm:ℝ) ≤ Z^(4:ℝ) ∧ (d.D.absNorm:ℝ) ≤ Z^(4:ℝ) ∧
      ∀(εfreq εvolume width : ℝ),|εfreq| ≤ 4 → width ≤ 1 →
        childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d.C d.D d.inactive
          Z 1 (Real.logb Z (volume s)) amp ξ reserve εfreq) εvolume 2+width ≤ 130 ∧
      ∃hP : d.R*(if second then d.D else d.C)≠0,
      ∃hPN : (((d.R*(if second then d.D else d.C)).absNorm:ℝ)) ≤ Z^Bmask,
      let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
      let base:=fun r : rows=>retainedState Z Bmask hZ
        (if second then d.τ r.val.2.2.1⁻¹ else d.τ r.val.2.1) Q₀
        (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
      let st:=fun r=>widenHighState (base r) bΦ hbΦ
      ∃keep : ∀r : rows,(st r).radial.keep (signed r),
      ∃select : rows→BufferIndex e,∀r : rows,
        (st r).width ≤ 2 ∧
        1 ≤ ((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
        (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0 ∧
        GeometryZeroBin M H hH (st r) η₀ hQM hQη (signed r) (keep r) e (Z^τ) (select r) := by
  filter_upwards [eventual_actual_geometry_main_nonzero_high_source_caps (Fintype.card α)
    b bs loss hb hbs hloss hloss1,
    eventual_high_width_one_gate η (Fintype.card α) b,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hc hw ht
  refine ⟨hc.1,?_⟩
  intro hZ reflected second s hη seed amp reserve t hend hseed hs₁ hs₂ hsource hvolume
    ha hr hA habs hω bin χ₀ Q₀ hQ₀ m hm hml hm2 hQM hQη hβlo hβhi j hK d ordinary rows l
  have caps:=hc.2 reflected s 1 seed 1 amp ξ reserve t hZ (le_refl _) hend hseed hs₁ hs₂
    hsource hvolume bin χ₀ Q₀ m j
  refine ⟨caps.1,caps.2.1,caps.2.2.1,caps.2.2.2,?_⟩
  intro εfreq εvolume width hεfreq hwidth
  have hg:=high_child_coordinate_ceiling reflected (!reflected) second l
    (geometryFirstSource s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val.1).hC
    (geometryFirstSource s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val.1).hD
    d.C d.D d.hC d.hD d.sameSupport d.inactive Z 1 (Real.logb Z (volume s))
    amp ξ reserve εfreq εvolume width hZ ⟨caps.1,caps.2.1⟩ ⟨caps.2.2.1,caps.2.2.2⟩
    (by norm_num) hA habs hω hεfreq hwidth
  refine ⟨hg,?_⟩
  have hR : d.R≠0:=by
    change (1:Ideal O)*geometryColumnIdeal reflected s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val≠0
    simp only [one_mul]
    cases reflected
    · exact (geometryFirstSource s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val.1).hC.1
    · exact (geometryFirstSource s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val.1).hD.1
  have hP : d.R*(if second then d.D else d.C)≠0:=mul_ne_zero hR (by
    cases second
    · exact d.hC.1
    · exact d.hD.1)
  have hfirst : (d.R.absNorm:ℝ) ≤ Z^(4:ℝ):=by
    change (((1:Ideal O)*geometryColumnIdeal reflected s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val).absNorm:ℝ) ≤ _
    simp only [one_mul]
    cases reflected
    · exact caps.1
    · exact caps.2.1
  have hsecond : ((if second then d.D else d.C).absNorm:ℝ) ≤ Z^(4:ℝ):=by
    cases second
    · exact caps.2.2.1
    · exact caps.2.2.2
  have hPN : (((d.R*(if second then d.D else d.C)).absNorm:ℝ)) ≤ Z^Bmask:=by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^(4:ℝ)*Z^(4:ℝ):=mul_le_mul hfirst hsecond (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _=Z^(8:ℝ):=by rw [←Real.rpow_add (zero_lt_one.trans hZ)]; norm_num
      _ ≤ Z^Bmask:=Real.rpow_le_rpow_of_exponent_le hZ.le hmask
  refine ⟨hP,hPN,?_⟩
  intro signed base st
  obtain ⟨keep,select,hs⟩:=actual_main_high_widened_selector M H hH (fun _:Unit=>d) (fun _=>χ₀)
    Q₀ hQ₀ m hm hml hm2 Z Bmask bΦ hZ hbΦ second (fun _=>hP) (fun _=>hPN)
    η₀ hQM hQη e (Z^τ) he ht hβlo hβhi
  refine ⟨keep,select,?_⟩
  intro r
  have hw':=(actual_geometry_second_width reflected s 1 seed (Z^(1:ℝ)) Z ξ amp reserve b
    (Fintype.card α) hK hZ (zero_lt_one.trans_le hb) bin j.val.1.1.val ordinary r
    (by rfl) (by rfl) Bmask
    (if second then r.val.2.2.1⁻¹ else r.val.2.1) Q₀
    (d.R*(if second then d.D else d.C)) hP hPN)
  have hw'' : (retainedState Z Bmask hZ (d.τ (if second then r.val.2.2.1⁻¹ else r.val.2.1)) Q₀
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive).width ≤ 2 := by
    apply hw'.trans
    dsimp only
    rw [show Real.logb Z (Z^(1:ℝ))=Real.logb Z Z by rw [Real.rpow_one],hη]
    exact hw.2 d.C d.D d.hC d.inactive _ _ amp reserve ξ ha hr hξ hξ1
  have widthBound : (st r).width ≤ 2 := by
    cases second <;> exact hw''

  exact ⟨widthBound,(hs r).1,(hs r).2.1,(hs r).2.2.2⟩

/-- A single selector and literal widened state on the entire original-nonzero
ordinary family, before either projector or high-buffer restriction. -/
theorem eventually_actual_main_high_canonical_admission
    {α : Type} [Fintype α] [DecidableEq α]
    (η : Character)(b bs loss ξ τ e Bmask bΦ : ℝ)
    (hb : 1 ≤ b)(hbs : 1 ≤ bs)(hloss : 0<loss)(hloss1 : loss ≤ 1)
    (hξ : 0 ≤ ξ)(hξ1 : ξ ≤ 1)(hτ : 0<τ)(he : 0<e)(hmask : 8 ≤ Bmask)(hbΦ : 2 ≤ bΦ)
    (η₀ : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(reflected second : Bool)(s : Input α)(_hη : s.η=η)
        (seed : Ideal O)(amp reserve t : ℝ),
      Endpoints b bs bs s → Squarefree seed →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      sourceRadius s ≤ Z^(3:ℝ) → volume s ≤ Z^(3:ℝ) → 0 ≤ amp → 0 ≤ reserve →
      |Real.logb Z (volume s)| ≤ 4 → |amp| ≤ 4 → |frequencyLoss Z 32 ξ+reserve| ≤ 4 →
      ∀(bin : ℤ×(Fin 5→ℤ)),
      let DataLabel:=geometryMainNonzeroBlocks reflected s 1 seed Z 1 amp ξ reserve b t
        (Fintype.card α) hZ bin hs₁ hs₂
      ∀(χ₀ : DataLabel→RayCharacter)(Q₀ : DataLabel→Ideal O)
        (_hQ₀ : ∀j,Q₀ j ≤ Ideal.span {(72:O)})(m : DataLabel→O)(_hm : ∀j,m j≠0)
        (_hml : ∀j,ConcretePrimeRowBridge.goodLambda∣m j)(_hm2 : ∀j,(2:O)∣m j)
        (hQM : ∀j,Q₀ j ≤ M)(hQη : ∀j,Q₀ j ≤ η₀.modulus)
        (_hβlo : 51/100 ≤ HeckeZeroSupremum.beta)(_hβhi : HeckeZeroSupremum.beta ≤ 7/8),
      let full:=fun j : DataLabel=>geometryLowSecondDatum reflected s 1 seed Z 1 amp ξ reserve b t
        (Fintype.card α) hZ bin j.val.1 hs₁ hs₂ j.val.2
      let ordinary:=fun j=>ordinarySecondDatum (full j) (χ₀ j) (Q₀ j) (m j)
      let rows:=secondLiveRows (fun j=>(ordinary j).block)
      ∃hP : ∀j,(full j).R*(if second then (full j).D else (full j).C)≠0,
      ∃hPN : ∀j,((((full j).R*(if second then (full j).D else (full j).C)).absNorm:ℝ)) ≤ Z^Bmask,
      let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
      let base:=fun r : rows=>retainedState Z Bmask hZ
        (if second then (full r.val.1).τ r.val.2.2.1⁻¹ else (full r.val.1).τ r.val.2.1) (Q₀ r.val.1)
        ((full r.val.1).R*(if second then (full r.val.1).D else (full r.val.1).C))
        (hP r.val.1) (hPN r.val.1) (full r.val.1).radius (full r.val.1).C (full r.val.1).D (full r.val.1).inactive
      let st:=fun r=>widenHighState (base r) bΦ hbΦ
      ∃keep : ∀r : rows,(st r).radial.keep (signed r),
      ∃select : rows→BufferIndex e,∀r : rows,
        (st r).width ≤ 2 ∧
        1 ≤ ((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
        (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0 ∧
        GeometryZeroBin M H hH (st r) η₀ (hQM r.val.1) (hQη r.val.1) (signed r) (keep r) e (Z^τ) (select r) ∧
        ((select r).1.val:ℝ) ≤ Z^τ := by
  filter_upwards [eventually_actual_main_high_literal_admission (α:=α) M H hH η b bs loss ξ τ e Bmask bΦ
    hb hbs hloss hloss1 hξ hξ1 hτ he hmask hbΦ η₀,
    eventual_high_width_one_gate η (Fintype.card α) b,
    eventually_geometry_zero_heights e τ hτ] with Z had hw hheights
  have ht:=hheights.2.1
  refine ⟨had.1,?_⟩
  intro hZ reflected second s hη seed amp reserve t hend hseed hs₁ hs₂ hsource hvolume ha hr hA hamp hω
    bin DataLabel χ₀ Q₀ hQ₀ m hm hml hm2 hQM hQη hβlo hβhi full ordinary rows
  have masks : ∀j : DataLabel,∃hP : (full j).R*(if second then (full j).D else (full j).C)≠0,
      ∃hPN : ((((full j).R*(if second then (full j).D else (full j).C)).absNorm:ℝ)) ≤ Z^Bmask,True := by
    intro j
    have hj:=had.2 hZ reflected second s hη seed amp reserve t hend hseed hs₁ hs₂
      hsource hvolume ha hr hA hamp hω bin (χ₀ j) (Q₀ j) (hQ₀ j) (m j) (hm j) (hml j) (hm2 j) (hQM j) (hQη j) hβlo hβhi j
    obtain ⟨hP,hPN,hstate⟩:=(hj.2.2.2.2 0 0 0 (by norm_num) (by norm_num)).2
    exact ⟨hP,hPN,True.intro⟩
  choose hP hPN htr using masks
  refine ⟨hP,hPN,?_⟩
  intro signed base st
  have hadmission (r : rows):=actual_main_ordinary_row_admission (full r.val.1)
    (χ₀ r.val.1) r.val.2.1 r.val.2.2.1 (Q₀ r.val.1) (hQ₀ r.val.1)
    (m r.val.1) (hm r.val.1) (hml r.val.1) (hm2 r.val.1) Z Bmask hZ second
    (hP r.val.1) (hPN r.val.1) r.val.2.2.2.val r.val.2.2.2.property
  let keep : ∀r : rows,(st r).radial.keep (signed r):=fun r=>(hadmission r).1
  have hp (r : rows):=actual_geometry_zero_partition M H hH (st r) η₀
    (hQM r.val.1) (hQη r.val.1) (signed r) (keep r) e (Z^τ) he ht hβlo hβhi
  let select : rows→BufferIndex e:=fun r=>Classical.choose (hp r)
  refine ⟨keep,select,?_⟩
  intro r
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  have hwidth:=(actual_geometry_second_width reflected s 1 seed (Z^(1:ℝ)) Z ξ amp reserve b
    (Fintype.card α) hK hZ (zero_lt_one.trans_le hb) bin r.val.1.val.1.1.val ordinary r
    (by rfl) (by rfl) Bmask
    (if second then r.val.2.2.1⁻¹ else r.val.2.1) (Q₀ r.val.1)
    ((full r.val.1).R*(if second then (full r.val.1).D else (full r.val.1).C))
    (hP r.val.1) (hPN r.val.1))
  have hw' : (retainedState Z Bmask hZ ((full r.val.1).τ (if second then r.val.2.2.1⁻¹ else r.val.2.1)) (Q₀ r.val.1)
      ((full r.val.1).R*(if second then (full r.val.1).D else (full r.val.1).C))
      (hP r.val.1) (hPN r.val.1) (full r.val.1).radius (full r.val.1).C (full r.val.1).D (full r.val.1).inactive).width ≤ 2 := by
    apply hwidth.trans
    dsimp only
    rw [show Real.logb Z (Z^(1:ℝ))=Real.logb Z Z by rw [Real.rpow_one],hη]
    exact hw.2 (full r.val.1).C (full r.val.1).D (full r.val.1).hC (full r.val.1).inactive _ _ amp reserve ξ ha hr hξ hξ1
  have hwidth' : (st r).width ≤ 2 := by cases second <;> exact hw'
  have hweight : 1 ≤ ((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re:=(hadmission r).2
  have hnonzero : (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0:=by
    intro hz
    rw [hz] at hweight
    norm_num at hweight
  exact ⟨hwidth',hweight,hnonzero,Classical.choose_spec (hp r),hheights.2.2 (select r)⟩

/-- The original block union is fixed before ordinary row or buffer selection. -/
@[irreducible] def mainHighProjectorUnion
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→SecondInputDatum α) : Finset (Ideal O):=
  sharedProjectors (fun j=>(datum j).block.divisors.filter Squarefree)

theorem main_high_residual_subset_union
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→SecondInputDatum α)
    (r : SecondRow (fun j=>(datum j).block)) :
    secondResidualIdeals (fun j=>(datum j).block) r⊆mainHighProjectorUnion datum := by
  intro L hL
  rw [mainHighProjectorUnion]
  apply mem_sharedProjectors _ r.1 L
  exact Finset.mem_filter.mpr ((mem_second_residual_ideals _ r L).mp hL)

theorem main_high_residual_sum_le_union
    {α Label κ : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→SecondInputDatum α)
    (row : κ→SecondRow (fun j=>(datum j).block))
    (labels : Finset κ)(cost : κ→Ideal O→ℝ)
    (hcost : ∀l∈labels,∀L,0 ≤ cost l L) :
    (∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l),cost l L) ≤ 
      ∑l∈labels,∑L∈mainHighProjectorUnion datum,cost l L := by
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum_of_subset_of_nonneg (main_high_residual_subset_union datum (row l))
  exact fun L _ _=>hcost l hl L

/-- The full original-nonzero ordinary carrier has one squarefree projector
union. Its cap follows from the original pools and survives later row/bin selection. -/
theorem actual_main_high_original_projector_union
    {α Label : Type} [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z D amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
    (χ₀ : Label→RayCharacter)(Q₀ : Label→Ideal O)(m : Label→O)
    (index : Label→GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b t N hZ bin)
    (U : ℝ)(hU : 0 ≤ U)
    (hn : Fintype.card α ≤ N)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ) ≤ Z^U) :
    let datum:=fun j : Label=>geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ (χ₀ j) (Q₀ j) (m j) (index j)
    let projectors:=mainHighProjectorUnion datum
    ∀L∈projectors,Squarefree L ∧ (L.absNorm:ℝ) ≤ Z^(((N:ℝ)+2)*U) := by
  intro datum projectors L hL
  change L∈mainHighProjectorUnion datum at hL
  rw [mainHighProjectorUnion] at hL
  obtain ⟨j,_,hr⟩:=Finset.mem_biUnion.mp hL
  have hres:=Finset.mem_filter.mp hr
  refine ⟨hres.2,?_⟩
  let q:=index j
  let base:=geometryLowSecondDatum reflected s R seed Z D amp ξ reserve b t N hZ bin q.1 hs₁ hs₂ q.2
  have hslots : Fintype.card base.slots ≤ N:=by
    change Fintype.card (liveIndices q.1.2.val) ≤ N
    exact (Fintype.card_subtype_le _).trans hn
  have hp : ∀i I,I∈base.input.pools i→(I.absNorm:ℝ) ≤ Z^U:=by
    change ∀i I,I∈(geometryLowFirstChild reflected s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q.1).pools i→(I.absNorm:ℝ) ≤ Z^U
    exact actual_child_pool_cap s
      (geometryColumnIdeal reflected s R seed (Z^D) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.1.val)
      R q.1.2
      (geometryColumnCharacter reflected s R seed (Z^D) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.1.val)
      t (Z^U) hpool
  exact (ordinary_second_projector_cap base N Z U hslots hZ.le hU hp (χ₀ j) (Q₀ j) (m j) L hres.1).2

/-- The literal retained block pays its seed in either selected ideal. -/
theorem actual_main_high_seed_gates
    {α : Type} [Fintype α] [DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z D amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
    (χ₀ : RayCharacter)(Q₀ : Ideal O)(m : O)
    (j : GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b t N hZ bin) :
    let d:=geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ χ₀ Q₀ m j
    d.seed∣d.C ∧ d.seed∣d.D := by
  intro d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D
  let label:=geometryFirstLabel s R seed (Z^D) Z ξ hK bin j.1.1.val
  have hseed1:=actual_first_live_squarefree (geometryFirstSource s R seed (Z^D) Z ξ hK bin)
    (fun _=>logAnnulus) j.1.1.val j.1.1.property
  have hg:=actual_retained_block_gates (liveIndices j.1.2.val)
    (geometryLowFirstChild reflected s R seed (Z^D) Z ξ hK bin t j.1)
    (R*geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin j.1.1.val) j.1.1.val.2.1.val
    hseed1 hs₁ hs₂
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve label)
    (firstMainFourierScale reflected (Z^D) (volume s) Z ξ (3*amp) reserve b N label) Z ξ
    (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) label) j.2
  exact ⟨hg.1,hg.2.1⟩

/-- The genuine high estimate applied to the literal ordinary family whose
carrier tests the original full block before restriction. Allocation support
and all first-child identities are derived from that carrier. -/
theorem actual_geometry_main_high_canonical_projectors {α : Type} [Fintype α] [DecidableEq α]
    (plane : Sil.Uneven.MainSource.Plane)
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : HeckeZeroSupremum.beta ≤ 7/8)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hQmax : Q ≤ 130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0 ≤ εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector U : ℝ) (hLprojector : 0 ≤ Lprojector) (hεprojector : 0<εprojector)
    (hU : 0 ≤ U)(hUL : ((N:ℝ)+2)*U ≤ Lprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      FineMarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 → 2*P.τ*(J+1) ≤ heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧ 0<Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ ampExponent reserveShift baseHeight : ℝ)
        (hK : 0<Z^D)(_hR : R≠0)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
        (hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      let DataLabel:=geometryMainNonzeroBlocks reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂
      letI : Fintype ↥DataLabel:=Finset.fintypeCoeSort DataLabel
      ∀(χ₀ : DataLabel→RayCharacter)(Q₀ : DataLabel→Ideal O)(m : DataLabel→O),
      let datum:=fun j : DataLabel=>geometryMainOrdinaryDatum reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂ (χ₀ j) (Q₀ j) (m j) j.val
      let first:=fun j : DataLabel=>geometryFirstLabel s R seed (Z^D) Z ξ hK bin j.val.1.1.val
      ∀row : κ→secondLiveRows (fun l=>(datum l).block),
      let column:=fun l=>(row l).val.1.val.1.1.val
      let hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l):=fun _=>rfl
      ∀ψ : κ→RayCharacter,
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (bAmpl rawError allowance Kcontrol width Wfiber : ℝ),
      0 ≤ ξ → 0 ≤ reserveShift → 0  ≤  Kcontrol → 0<width →
      0 ≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ) ≤ Wfiber) →
      ∀select : κ→BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width ≤ Q) →
      Squarefree seed → sourceRadius s ≤ Z^B → lo ≤  s.lower →
      Sil.Uneven.MainSource.widthLo ≤ bAmpl → bAmpl ≤ Sil.Uneven.MainSource.widthHi → D=1 → 0 ≤ D → |D| ≤ B → |A| ≤ B → |ampExponent| ≤ B →
      |frequencyLoss Z 32 ξ+reserveShift| ≤ B → frequencyLoss Z 32 ξ+reserveShift ≤ Sil.Uneven.MainSource.frequencyAllowance → εfreq ≤ B → ξ ≤ εfreq →
      A ≤ D*Sil.Uneven.MainSource.total plane bAmpl → ampExponent ≤ D*Sil.Uneven.MainSource.amp plane bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ) ≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ) ≤ Z^B) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀l∈labels,GeometryZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        P.e (Z^P.τ) (select l)) →
      (∀l∈labels,(1+plane.q)/2 ≤ bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      (∀l∈labels,((select l).1.val:ℝ) ≤ Z^P.τ) →
      Fintype.card α ≤ N → (∀j,s.M j ≤ Cs) →
      s.b₁ ≤ bs → s.b₂ ≤ bs → s.upper ≤ b →
      (∀j,logWindow (s.lo j) (s.hi j) ≤ window) →
      ∀(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(cap : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (1/50)*D ≤ ∑j,w j →
      (∑j,w j) ≤ 1/25 →
      bAmpl-Sil.Uneven.MainSource.widthMesh ≤ ∑j,w j →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      pad ≤ allowance →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  bootstrapRawMesh*fineRawCore) →
      (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ) ≤ Z^U) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2 ≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ) ≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l).val,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L) ≤ 
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(38*B+|εvolume|)/width⌋:ℤ) ⌊(38*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(mainHighReserve)+4*width+loss+rawError+allowance+B*εmass+heightloss)))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_buffered_projectors (α:=α) M H hH plane
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
     N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Lprojector εprojector hLprojector hεprojector
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hevent⟩:=
    hhigh heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hevent] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ reflected second s hη R seed W D ξ ampExponent reserveShift baseHeight hK hR hZ bin hs₁ hs₂
    DataLabel χ₀ Q₀ m datum first row column hfirst ψ left unit hf rawKey key bAmpl rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select A x hq hseed hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    t w σ v θ p cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    hwidth hradial hw hwmarked hwr hσlo hσhi hheight hplainheight hW hpool hcontrol hledger
    t₀ u hψ hshift
  let globalDs:=mainHighProjectorUnion datum
  let Ds : κ→Finset (Ideal O):=fun _=>globalDs
  let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
  let B₁ : ∀l,actualAllocations s.pools (C₁ l):=fun l=>(row l).val.1.val.1.2
  let t₁ : κ→ℝ:=fun _=>baseHeight
  have hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l):=fun _=>rfl
  have hR' : ∀l,(datum (row l).val.1).R≠0:=fun l=>actual_geometry_child_puncture_ne_zero
    reflected s R seed hR (Z^D) Z ξ hK bin (column l)
  have hradius : ∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
    (firstMainFourierScale reflected (Z^D) (volume s) Z ξ (3*ampExponent)
      reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ:=fun _ _=>rfl
  have hf₁ : ∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0:=by
    intro l _
    exact (Finset.mem_filter.mp (row l).val.1.property).2.1
  have hprojectors:=actual_main_high_original_projector_union reflected s R seed
    Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂ χ₀ Q₀ m (fun j : DataLabel=>j.val) U hU hcard hpool
  have hDs : ∀l∈labels,∀L∈Ds l,Squarefree L:=fun _ _ L hL=>(hprojectors L hL).1
  have hnormL : ∀l∈labels,∀L∈Ds l,(L.absNorm:ℝ) ≤ Z^Lprojector:=fun _ _ L hL=>
    (hprojectors L hL).2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hUL)
  let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
  have hseed₂ : ∀l∈labels,(datum (row l).val.1).seed∣E l:=by
    intro l _
    have h:=actual_main_high_seed_gates reflected s R seed Z D ampExponent ξ reserveShift b baseHeight
      N hZ bin hs₁ hs₂ (χ₀ (row l).val.1) (Q₀ (row l).val.1) (m (row l).val.1) (row l).val.1.val
    cases second
    · exact h.1
    · exact h.2
  have hpaid:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR' ψ
    ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select hq
    hseed hs₁ hs₂ hsource hlower hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ (fun l=>(datum (row l).val.1).seed) t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    hseed₂ hwidth hradial hw hwmarked hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u (fun _ _=>rfl) (fun _ _=>HEq.rfl) (fun _ _=>rfl) (fun _ _=>rfl) hψ hshift
  apply (mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans hpaid
  apply main_high_residual_sum_le_union datum (fun l=>(row l).val) labels
  intro l _ L
  dsimp only [mainNormalizedPhysicalCost]
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact div_nonneg (uneven_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l) (zero_lt_one.trans hZ).le)
          (volume_pos (datum (row l).val.1).input).le
      · exact div_nonneg (datum (row l).val.1).K_pos.le (lowerFactor_pos N lo ap hlo hap).le
    · exact (normalizer_pos _ _ (datum (row l).val.1).hC _).le
  · split <;> exact sq_nonneg _

end
end OAI.SevenEighths.MainHigh






