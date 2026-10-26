/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B109
import Candidate.Bundles.B163
import Candidate.Bundles.B166
import Candidate.Bundles.B172
import Candidate.Bundles.B173
import Candidate.Bundles.B176
import Candidate.Bundles.B177

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighPayment; sha256 90fb4fe77be9c66191e67713492dfb67b8cb7a6a3c9c79924b007362cd0e0120 -/
section
                                                                    
                                                              
                                                            
                                                                 
                                                             
                                                           
                                    

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
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


open Cycle61FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle61Moment.LowBranch

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Literal original-nonzero physical second blocks supply the small norm
caps, retained puncture budget, actual unit profile, fixed width ceiling,
and one full buffered selector. The threshold precedes all block labels. -/
theorem eventually_actual_main_high_literal_admission
    {α : Type} [Fintype α] [DecidableEq α]
    (η : Character)(b bs loss ξ τ e Bmask bΦ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hloss : 0< loss)(hloss1 : loss≤1)
    (hξ : 0≤ξ)(hξ1 : ξ≤1)(hτ : 0<τ)(he : 0< e)(hmask : 8≤ Bmask)(hbΦ : 2≤ bΦ)
    (η₀ : Character) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(hZ : 1< Z)(reflected second : Bool)(s : Input α)(_hη : s.η=η)
        (seed : Ideal O)(amp reserve t : ℝ),
      Endpoints b bs bs s → Squarefree seed →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      sourceRadius s≤ Z^(3:ℝ) → volume s≤ Z^(3:ℝ) → 0≤ amp → 0≤ reserve →
      |Real.logb Z (volume s)|≤4 → |amp|≤4 → |frequencyLoss Z 32 ξ+reserve|≤4 →
      ∀(bin : ℤ×(Fin 5→ℤ))(χ₀ : RayCharacter)(Q₀ : Ideal O)
        (_hQ₀ : Q₀≤ Ideal.span {(72:O)})(m : O)(_hm : m≠0)
        (_hml : ConcretePrimeRowBridge.goodLambda∣m)(_hm2 : (2:O)∣m)
        (hQM : Q₀≤ M)(hQη : Q₀≤η₀.modulus)
        (_hβlo : 51/100≤ HeckeZeroSupremum.beta)(_hβhi : HeckeZeroSupremum.beta≤7/8)
        (j : geometryMainNonzeroBlocks reflected s 1 seed Z 1 amp ξ reserve b t
          (Fintype.card α) hZ bin hs₁ hs₂),
      let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
      let d:=geometryLowSecondDatum reflected s 1 seed Z 1 amp ξ reserve b t
        (Fintype.card α) hZ bin j.val.1 hs₁ hs₂ j.val.2
      let ordinary:=fun _:Unit=>ordinarySecondDatum d χ₀ Q₀ m
      let rows:=secondLiveRows (fun l=>(ordinary l).block)
      let l:=geometryFirstLabel s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val
      (l.1.1.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤ Z^(4:ℝ) ∧
      (d.C.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (d.D.absNorm:ℝ)≤ Z^(4:ℝ) ∧
      ∀(εfreq εvolume width : ℝ),|εfreq|≤4 → width≤1 →
        childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d.C d.D d.inactive
          Z 1 (Real.logb Z (volume s)) amp ξ reserve εfreq) εvolume 2+width≤130 ∧
      ∃hP : d.R*(if second then d.D else d.C)≠0,
      ∃hPN : (((d.R*(if second then d.D else d.C)).absNorm:ℝ))≤ Z^Bmask,
      let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
      let base:=fun r : rows=>retainedState Z Bmask hZ
        (if second then d.τ r.val.2.2.1⁻¹ else d.τ r.val.2.1) Q₀
        (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
      let st:=fun r=>widenHighState (base r) bΦ hbΦ
      ∃keep : ∀r : rows,(st r).radial.keep (signed r),
      ∃select : rows→ BufferIndex e,∀r : rows,
        (st r).width≤2 ∧
        1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
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
  have hfirst : (d.R.absNorm:ℝ)≤ Z^(4:ℝ):=by
    change (((1:Ideal O)*geometryColumnIdeal reflected s 1 seed (Z^(1:ℝ)) Z ξ hK bin j.val.1.1.val).absNorm:ℝ)≤ _
    simp only [one_mul]
    cases reflected
    · exact caps.1
    · exact caps.2.1
  have hsecond : ((if second then d.D else d.C).absNorm:ℝ)≤ Z^(4:ℝ):=by
    cases second
    · exact caps.2.2.1
    · exact caps.2.2.2
  have hPN : (((d.R*(if second then d.D else d.C)).absNorm:ℝ))≤ Z^Bmask:=by
    rw [map_mul,Nat.cast_mul]
    calc
      _≤ Z^(4:ℝ)*Z^(4:ℝ):=mul_le_mul hfirst hsecond (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _=Z^(8:ℝ):=by rw [←Real.rpow_add (zero_lt_one.trans hZ)]; norm_num
      _≤ Z^Bmask:=Real.rpow_le_rpow_of_exponent_le hZ.le hmask
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
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive).width≤2 := by
    apply hw'.trans
    dsimp only
    rw [show Real.logb Z (Z^(1:ℝ))=Real.logb Z Z by rw [Real.rpow_one],hη]
    exact hw.2 d.C d.D d.hC d.inactive _ _ amp reserve ξ ha hr hξ hξ1
  have widthBound : (st r).width≤2 := by
    cases second <;> exact hw''

  exact ⟨widthBound,(hs r).1,(hs r).2.1,(hs r).2.2.2⟩

/-- A single selector and literal widened state on the entire original-nonzero
ordinary family, before either projector or high-buffer restriction. -/
theorem eventually_actual_main_high_canonical_admission
    {α : Type} [Fintype α] [DecidableEq α]
    (η : Character)(b bs loss ξ τ e Bmask bΦ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hloss : 0< loss)(hloss1 : loss≤1)
    (hξ : 0≤ξ)(hξ1 : ξ≤1)(hτ : 0<τ)(he : 0< e)(hmask : 8≤ Bmask)(hbΦ : 2≤ bΦ)
    (η₀ : Character) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(hZ : 1< Z)(reflected second : Bool)(s : Input α)(_hη : s.η=η)
        (seed : Ideal O)(amp reserve t : ℝ),
      Endpoints b bs bs s → Squarefree seed →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      sourceRadius s≤ Z^(3:ℝ) → volume s≤ Z^(3:ℝ) → 0≤ amp → 0≤ reserve →
      |Real.logb Z (volume s)|≤4 → |amp|≤4 → |frequencyLoss Z 32 ξ+reserve|≤4 →
      ∀(bin : ℤ×(Fin 5→ℤ)),
      let DataLabel:=geometryMainNonzeroBlocks reflected s 1 seed Z 1 amp ξ reserve b t
        (Fintype.card α) hZ bin hs₁ hs₂
      ∀(χ₀ : DataLabel→ RayCharacter)(Q₀ : DataLabel→ Ideal O)
        (_hQ₀ : ∀j,Q₀ j≤ Ideal.span {(72:O)})(m : DataLabel→ O)(_hm : ∀j,m j≠0)
        (_hml : ∀j,ConcretePrimeRowBridge.goodLambda∣m j)(_hm2 : ∀j,(2:O)∣m j)
        (hQM : ∀j,Q₀ j≤ M)(hQη : ∀j,Q₀ j≤η₀.modulus)
        (_hβlo : 51/100≤ HeckeZeroSupremum.beta)(_hβhi : HeckeZeroSupremum.beta≤7/8),
      let full:=fun j : DataLabel=>geometryLowSecondDatum reflected s 1 seed Z 1 amp ξ reserve b t
        (Fintype.card α) hZ bin j.val.1 hs₁ hs₂ j.val.2
      let ordinary:=fun j=>ordinarySecondDatum (full j) (χ₀ j) (Q₀ j) (m j)
      let rows:=secondLiveRows (fun j=>(ordinary j).block)
      ∃hP : ∀j,(full j).R*(if second then (full j).D else (full j).C)≠0,
      ∃hPN : ∀j,((((full j).R*(if second then (full j).D else (full j).C)).absNorm:ℝ))≤ Z^Bmask,
      let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
      let base:=fun r : rows=>retainedState Z Bmask hZ
        (if second then (full r.val.1).τ r.val.2.2.1⁻¹ else (full r.val.1).τ r.val.2.1) (Q₀ r.val.1)
        ((full r.val.1).R*(if second then (full r.val.1).D else (full r.val.1).C))
        (hP r.val.1) (hPN r.val.1) (full r.val.1).radius (full r.val.1).C (full r.val.1).D (full r.val.1).inactive
      let st:=fun r=>widenHighState (base r) bΦ hbΦ
      ∃keep : ∀r : rows,(st r).radial.keep (signed r),
      ∃select : rows→ BufferIndex e,∀r : rows,
        (st r).width≤2 ∧
        1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
        (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0 ∧
        GeometryZeroBin M H hH (st r) η₀ (hQM r.val.1) (hQη r.val.1) (signed r) (keep r) e (Z^τ) (select r) ∧
        ((select r).1.val:ℝ)≤ Z^τ := by
  filter_upwards [eventually_actual_main_high_literal_admission (α:=α) M H hH η b bs loss ξ τ e Bmask bΦ
    hb hbs hloss hloss1 hξ hξ1 hτ he hmask hbΦ η₀,
    eventual_high_width_one_gate η (Fintype.card α) b,
    eventually_geometry_zero_heights e τ hτ] with Z had hw hheights
  have ht:=hheights.2.1
  refine ⟨had.1,?_⟩
  intro hZ reflected second s hη seed amp reserve t hend hseed hs₁ hs₂ hsource hvolume ha hr hA hamp hω
    bin DataLabel χ₀ Q₀ hQ₀ m hm hml hm2 hQM hQη hβlo hβhi full ordinary rows
  have masks : ∀j : DataLabel,∃hP : (full j).R*(if second then (full j).D else (full j).C)≠0,
      ∃hPN : ((((full j).R*(if second then (full j).D else (full j).C)).absNorm:ℝ))≤ Z^Bmask,True := by
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
  let select : rows→ BufferIndex e:=fun r=>Classical.choose (hp r)
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
      (hP r.val.1) (hPN r.val.1) (full r.val.1).radius (full r.val.1).C (full r.val.1).D (full r.val.1).inactive).width≤2 := by
    apply hwidth.trans
    dsimp only
    rw [show Real.logb Z (Z^(1:ℝ))=Real.logb Z Z by rw [Real.rpow_one],hη]
    exact hw.2 (full r.val.1).C (full r.val.1).D (full r.val.1).hC (full r.val.1).inactive _ _ amp reserve ξ ha hr hξ hξ1
  have hwidth' : (st r).width≤2 := by cases second <;> exact hw'
  have hweight : 1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re:=(hadmission r).2
  have hnonzero : (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0:=by
    intro hz
    rw [hz] at hweight
    norm_num at hweight
  exact ⟨hwidth',hweight,hnonzero,Classical.choose_spec (hp r),hheights.2.2 (select r)⟩

/-- The original block union is fixed before ordinary row or buffer selection. -/
@[irreducible] def mainHighProjectorUnion
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→ SecondInputDatum α) : Finset (Ideal O):=
  sharedProjectors (fun j=>(datum j).block.divisors.filter Squarefree)

theorem main_high_residual_subset_union
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→ SecondInputDatum α)
    (r : SecondRow (fun j=>(datum j).block)) :
    secondResidualIdeals (fun j=>(datum j).block) r⊆mainHighProjectorUnion datum := by
  intro L hL
  rw [mainHighProjectorUnion]
  apply mem_sharedProjectors _ r.1 L
  exact Finset.mem_filter.mpr ((mem_second_residual_ideals _ r L).mp hL)

theorem main_high_residual_sum_le_union
    {α Label κ : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→ SecondInputDatum α)
    (row : κ→ SecondRow (fun j=>(datum j).block))
    (labels : Finset κ)(cost : κ→ Ideal O→ℝ)
    (hcost : ∀l∈labels,∀L,0≤ cost l L) :
    (∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l),cost l L)≤
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
    (Z D amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1< Z)
    (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
    (χ₀ : Label→ RayCharacter)(Q₀ : Label→ Ideal O)(m : Label→ O)
    (index : Label→ GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b t N hZ bin)
    (U : ℝ)(hU : 0≤ U)
    (hn : Fintype.card α≤ N)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) :
    let datum:=fun j : Label=>geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ (χ₀ j) (Q₀ j) (m j) (index j)
    let projectors:=mainHighProjectorUnion datum
    ∀L∈projectors,Squarefree L ∧ (L.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  intro datum projectors L hL
  change L∈mainHighProjectorUnion datum at hL
  rw [mainHighProjectorUnion] at hL
  obtain ⟨j,_,hr⟩:=Finset.mem_biUnion.mp hL
  have hres:=Finset.mem_filter.mp hr
  refine ⟨hres.2,?_⟩
  let q:=index j
  let base:=geometryLowSecondDatum reflected s R seed Z D amp ξ reserve b t N hZ bin q.1 hs₁ hs₂ q.2
  have hslots : Fintype.card base.slots≤ N:=by
    change Fintype.card (liveIndices q.1.2.val)≤ N
    exact (Fintype.card_subtype_le _).trans hn
  have hp : ∀i I,I∈base.input.pools i→(I.absNorm:ℝ)≤ Z^U:=by
    change ∀i I,I∈(geometryLowFirstChild reflected s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q.1).pools i→(I.absNorm:ℝ)≤ Z^U
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
    (Z D amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1< Z)
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
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector U : ℝ) (hLprojector : 0≤ Lprojector) (hεprojector : 0<εprojector)
    (hU : 0≤ U)(hUL : ((N:ℝ)+2)*U≤ Lprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain → 2*P.τ*(J+1)≤ heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ ampExponent reserveShift baseHeight : ℝ)
        (hK : 0< Z^D)(_hR : R≠0)(hZ : 1< Z)(bin : ℤ×(Fin 5→ℤ))
        (hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),
      let DataLabel:=geometryMainNonzeroBlocks reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂
      letI : Fintype ↥DataLabel:=Finset.fintypeCoeSort DataLabel
      ∀(χ₀ : DataLabel→ RayCharacter)(Q₀ : DataLabel→ Ideal O)(m : DataLabel→ O),
      let datum:=fun j : DataLabel=>geometryMainOrdinaryDatum reflected s R seed Z D ampExponent ξ reserveShift b baseHeight N hZ bin hs₁ hs₂ (χ₀ j) (Q₀ j) (m j) j.val
      let first:=fun j : DataLabel=>geometryFirstLabel s R seed (Z^D) Z ξ hK bin j.val.1.1.val
      ∀row : κ→ secondLiveRows (fun l=>(datum l).block),
      let column:=fun l=>(row l).val.1.val.1.1.val
      let hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l):=fun _=>rfl
      ∀ψ : κ→ RayCharacter,
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (bAmpl rawError allowance Kcontrol width Wfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      ∀select : κ→ BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀l∈labels,GeometryZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        P.e (Z^P.τ) (select l)) →
      (∀l∈labels,21/25≤ bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀l∈labels,((select l).1.val:ℝ)≤ Z^P.τ) →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      ∀(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈secondResidualIdeals (fun j=>(datum j).block) (row l).val,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass+heightloss)))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_buffered_projectors (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Lprojector εprojector hLprojector hεprojector
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hslot hplain hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hevent⟩:=
    hhigh heightloss P hboundeq hslot hplain hdensity
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hevent] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ reflected second s hη R seed W D ξ ampExponent reserveShift baseHeight hK hR hZ bin hs₁ hs₂
    DataLabel χ₀ Q₀ m datum first row column hfirst ψ left unit hf rawKey key bAmpl rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select A x hq hseed hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    t w σ v θ p cap hcap hmatches hscales hpadallow
    hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hpool hcontrol hledger
    t₀ u hψ hshift
  let globalDs:=mainHighProjectorUnion datum
  let Ds : κ→ Finset (Ideal O):=fun _=>globalDs
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
  have hnormL : ∀l∈labels,∀L∈Ds l,(L.absNorm:ℝ)≤ Z^Lprojector:=fun _ _ L hL=>
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
    hseed hs₁ hs₂ hsource hlower hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ (fun l=>(datum (row l).val.1).seed) t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u (fun _ _=>rfl) (fun _ _=>HEq.rfl) (fun _ _=>rfl) (fun _ _=>rfl) hψ hshift
  apply (mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans hpaid
  apply main_high_residual_sum_le_union datum (fun l=>(row l).val) labels
  intro l _ L
  dsimp only [mainNormalizedPhysicalCost]
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact div_nonneg (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l))
          (volume_pos (datum (row l).val.1).input).le
      · exact div_nonneg (datum (row l).val.1).K_pos.le (lowerFactor_pos N lo ap hlo hap).le
    · exact (normalizer_pos _ _ (datum (row l).val.1).hC _).le
  · split <;> exact sq_nonneg _

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_actual_main_high_literal_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_canonical_projectors

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_original_projector_union

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_actual_main_high_canonical_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_high_residual_subset_union
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_high_residual_sum_le_union

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_seed_gates

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowPayment; sha256 d4ad1e73dea94f903ba1420a4df5d5f5cd8002fd5e011cf5cac8b352a36614a6 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                 
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondInputCapacitySource
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentSectorLocalization
open CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open Cycle61FinalNatural CenteredMomentEnergyState Cycle61Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open LocalMoment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowPaymentSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- One common second allocation and one original row witness per original
nonzero block, selected before the complete row or ray sums. -/
theorem actual_main_low_family_choices {Label : Type*}
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : Label→ geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (second : Bool) :
    let d:=fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (j l).val.1 hz₁ hz₂ (j l).val.2
    ∃B₂ : (l : Label)→ actualAllocations (d l).input.pools (if second then (d l).D else (d l).C),
      ∃_rwitness : (l : Label)→ secondLiveRows (fun _:Unit=>(d l).block),
        ∀l,frozenCoefficient (B₂ l).val (if second then (d l).D else (d l).C) (d l).R
          (d l).input.ν (d l).input.W (d l).input.P≠0 ∧
          (d l).inactive∈inactiveSubsets (d l).C (d l).D := by
  intro d
  have h (l : Label) := actual_geometry_main_low_choices reflected s R seed Z Mrow amp ξ reserve b t N hZ
    key hz₁ hz₂ (j l) second
  choose B₂ rwitness hgood using h
  exact ⟨B₂,rwitness,hgood⟩

/-- The complete second family for selected first allocations, filtered by
the ORIGINAL full physical block before any ordinary or zero-bin restriction. -/
def mainLowSelectedNonzeroRows {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :
    Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (firstIndex l)) :=
  Finset.univ.filter (fun r=>
    (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
      geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)

def mainLowSelectedOriginal {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (r : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ :=
  ⟨⟨firstIndex r.val.1,r.val.2⟩,(Finset.mem_filter.mp r.property).2⟩

/-- Original nonzero membership supplies the genuine inactive-subset gate
for every selected block. It never asks that the restricted block be nonzero. -/
theorem actual_main_low_selected_inactive {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (r : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    r.val.2.2.1∈inactiveSubsets r.val.2.1.val.val.1 r.val.2.1.val.val.2 := by
  exact (actual_geometry_main_original_admission reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
      firstIndex r)).2

/-- A literal buffered bin in the complete signed row set. -/
def mainLowPaymentRows (rows : Finset O) {e : ℝ}
    (select : rows→ BufferIndex e) (p : BufferIndex e) : Finset O :=
  (rows.attach.filter (fun z=>select z=p ∧ bufferValue e p<21/25)).image Subtype.val

theorem mem_main_low_payment_rows (rows : Finset O) {e : ℝ}
    (select : rows→ BufferIndex e) (p : BufferIndex e) (z : O) :
    z∈mainLowPaymentRows rows select p ↔
      ∃hz : z∈rows,select ⟨z,hz⟩=p ∧ bufferValue e p<21/25 := by
  simp only [mainLowPaymentRows,Finset.mem_image,Finset.mem_filter,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨x,hx,he⟩
    subst z
    exact ⟨x.property,hx⟩
  · rintro ⟨hz,hselect,hlow⟩
    exact ⟨⟨z,hz⟩,⟨hselect,hlow⟩,rfl⟩

theorem main_low_payment_rows_sum (rows : Finset O) {e : ℝ}
    (select : rows→ BufferIndex e) (p : BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if select z=p ∧ bufferValue e p<21/25 then f z.val else 0)=
      ∑z∈mainLowPaymentRows rows select p,f z := by
  rw [mainLowPaymentRows,Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · intro x _ y _ h
    exact Subtype.ext h

/-- All strict low rows occur in exactly one literal kernel bin. The
finite buffered index set is fixed before the moving rows or labels. -/
theorem main_low_payment_complete_low_sum (rows : Finset O) {e : ℝ}
    (select : rows→ BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if bufferValue e (select z)<21/25 then f z.val else 0)=
      ∑p : BufferIndex e,∑z∈mainLowPaymentRows rows select p,f z := by
  calc
    _=∑z : rows,∑p : BufferIndex e,
        if select z=p ∧ bufferValue e p<21/25 then f z.val else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [ite_and]
      simp
    _=∑p : BufferIndex e,∑z : rows,
        if select z=p ∧ bufferValue e p<21/25 then f z.val else 0 := Finset.sum_comm
    _=_ := by
      apply Finset.sum_congr rfl
      intro p _
      exact main_low_payment_rows_sum rows select p f

/-- The genuine buffered partition supplies precisely the low kernel's
keep and low gates, and dominates literal unit weight, for each fixed bin.
The reflected ray and signed row are retained throughout. -/
theorem actual_main_low_payment_bins
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    ∃select : rows→ BufferIndex e,∀p z,z∈mainLowPaymentRows rows select p→
      st.radial.keep z ∧
      ActualLow M H hH st η₀ hQM hQη (21/25) e (3*(p.1.val+1:ℕ)*T) z ∧
      1≤(st.radial.profile (normValue z/st.radial.scale)).re ∧
      1≤ p.1.val ∧ p.1.val≤ bufferCount e := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (ha z).1 e T he hT hβlo hβhi
  let select : rows→ BufferIndex e := fun z=>Classical.choose (hp z)
  refine ⟨select,?_⟩
  intro p z hz
  obtain ⟨hzrows,hsel,hlow⟩ := (mem_main_low_payment_rows rows select p z).mp hz
  have hg:=ha ⟨z,hzrows⟩
  have hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T p := by
    have hb:=Classical.choose_spec (hp ⟨z,hzrows⟩)
    change GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T (select ⟨z,hzrows⟩) at hb
    rw [hsel] at hb
    exact hb
  refine ⟨hg.1,?_,hg.2.2,hbin.1,hbin.2.1⟩
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z hg.1 e T p hbin hlow
  simpa only [normValue_eq_embedding] using hg.2.2

/-- A single bounded shifted-height envelope is sufficient for every
occupied buffered bin. The bin index is chosen from genuine zero geometry. -/
theorem main_low_payment_height_bin {e : ℝ} (p : BufferIndex e)
    (hp : 1≤ p.1.val) (v height T : ℝ) (hT : 0≤ T)
    (hheight : |v|+height+T/2≤5*T) :
    |v|+height+T/2≤(3*p.1.val+2:ℕ)*T := by
  apply hheight.trans
  apply mul_le_mul_of_nonneg_right _ hT
  exact_mod_cast (show 5≤3*p.1.val+2 by omega)

/-- Both literal first-Mellin orientations fit the bounded kernel range.
The cutoff is common to all rows and does not restrict either shift globally. -/
theorem main_low_payment_shifted_height_envelope
    (second : Bool) (v height t u T : ℝ) (hT : 0≤ T)
    (hsmall : 2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤ T) :
    |v+2*Real.pi*(u-(if second then -t else t))|+height+T/2≤5*T := by
  have hs : |u-(if second then -t else t)|≤|u|+|t| := by
    cases second
    · simpa using abs_sub_le u 0 t
    · simpa using abs_sub_le u 0 (-t)
  have hmul : |2*Real.pi*(u-(if second then -t else t))|≤
      2*Real.pi*(|u|+|t|) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hv := (abs_add_le v (2*Real.pi*(u-(if second then -t else t)))).trans
    (add_le_add (le_refl |v|) hmul)
  nlinarith

/-- The genuine positive selector index puts both shifted rays into the
same buffered height bin used by the original low kernel. -/
theorem main_low_payment_shifted_height_bin {e : ℝ} (p : BufferIndex e)
    (hp : 1≤ p.1.val) (second : Bool) (v height t u T : ℝ) (hT : 0≤ T)
    (hsmall : 2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤ T) :
    |v+2*Real.pi*(u-(if second then -t else t))|+height+T/2≤
      (3*p.1.val+2:ℕ)*T :=
  main_low_payment_height_bin p hp _ height T hT
    (main_low_payment_shifted_height_envelope second v height t u T hT hsmall)

/-- A strict small-tau inequality supplies the high-parameter gate for
EVERY member of the fixed finite zero-bin dictionary at one common threshold.
The threshold precedes source rows, characters, allocations and heights. -/
theorem eventual_main_low_payment_high_gate (e τ d η : ℝ)
    (hτ : 0<τ) (hgap : 2*τ< d*η) :
    ∀ᶠ Z : ℝ in Filter.atTop,1< Z ∧ 2< Z^τ ∧
      ∀p : BufferIndex e,(3+(3*p.1.val+2:ℕ)*Z^τ)^2≤(Z^d)^η := by
  let B : ℕ := 3*bufferCount e+2
  let K : ℝ := 3+(B:ℝ)
  have hg : 0< d*η-2*τ := sub_pos.mpr hgap
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (Filter.eventually_gt_atTop (2:ℝ)),
    (tendsto_rpow_atTop hg).eventually (Filter.eventually_ge_atTop (K^2))]
    with Z hZ hT hpower
  refine ⟨hZ,hT,?_⟩
  intro p
  have hz : 0< Z := zero_lt_one.trans hZ
  have hscale : 1≤ Z^τ := by linarith
  have hi : 3*p.1.val+2≤ B := by
    dsimp only [B]
    have hp := p.1.isLt
    omega
  have hic : ((3*p.1.val+2:ℕ):ℝ)≤(B:ℝ) := by exact_mod_cast hi
  have hbound : 3+(3*p.1.val+2:ℕ)*Z^τ≤ K*Z^τ := by
    have hm := mul_le_mul_of_nonneg_right hic (Real.rpow_nonneg hz.le τ)
    dsimp only [K]
    nlinarith
  have hsquare : (3+(3*p.1.val+2:ℕ)*Z^τ)^2≤(K*Z^τ)^2 :=
    pow_le_pow_left₀ (by positivity) hbound 2
  calc
    (3+(3*p.1.val+2:ℕ)*Z^τ)^2≤(K*Z^τ)^2 := hsquare
    _=K^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [mul_comm,Real.rpow_mul hz.le]
      exact (Real.rpow_two _).symm
    _≤ Z^(d*η-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hz.le _)
    _=Z^(d*η) := by rw [←Real.rpow_add hz]; congr 1; ring
    _=(Z^d)^η := by rw [Real.rpow_mul hz.le]

/-- The fixed physical lower factor stays outside the complete selected
family. There is no arithmetic-label cardinality or extra source volume. -/
theorem main_low_payment_physical_factor {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (zs : Label→ Finset O) (f : Label→ Ideal O→ O→ℝ) :
    (∑l,∑D∈(d l).block.divisors.filter Squarefree,
      (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
        (∑z∈zs l,f l D z))=
    (1/lowerFactor N a ap)*
      (∑l,∑D∈(d l).block.divisors.filter Squarefree,
        (coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)*
          (∑z∈zs l,f l D z)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_family_choices
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_selected_inactive
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_rows_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_complete_low_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_payment_bins
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_physical_factor
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_height_bin
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_shifted_height_envelope
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_payment_shifted_height_bin
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_main_low_payment_high_gate

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainSelectedRowEmbedding; sha256 d3c33c1252dff3ce12b4a80df697181b8f4ab0927af71ba3933ef76a822d9a60 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainSelectedRowEmbeddingSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
variable (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

/-- One selected first allocation per arithmetic-label/projector key embeds
into the literal ORIGINAL full-nonzero main family. The complete second
index, including all four dyads, is recovered by dependent sigma equality. -/
theorem main_low_selected_original_injective
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val))) :
    Function.Injective (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key hz₁ hz₂ firstIndex) := by
  intro q r h
  have hb := congrArg Subtype.val h
  change (⟨firstIndex q.val.1,q.val.2⟩ :
    GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)=
      ⟨firstIndex r.val.1,r.val.2⟩ at hb
  have hf : firstIndex q.val.1=firstIndex r.val.1 := congrArg Sigma.fst hb
  have hl : q.val.1=r.val.1 := hinj (congrArg (fun j : GeometryLowFirstIndex reflected s R seed
    (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key=>
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.val,j.1.val.2.1.val)) hf)
  apply Subtype.ext
  exact Sigma.ext hl (Sigma.mk.inj_iff.mp hb).2

/-- The selected carrier uses the actual datum, before ordinary restriction. -/
def mainLowSelectedDatum
    (q : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    SecondInputDatum α :=
  geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    (firstIndex q.val.1) hz₁ hz₂ q.val.2

theorem main_low_selected_original_datum
    (q : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q).val.1
      hz₁ hz₂
      (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q).val.2=
    mainLowSelectedDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q := rfl

/-- The same exact datum identity preserves both ordinary rays and their
original inducing exclusion. No nonzero ordinary block is required. -/
theorem main_low_selected_original_ordinary_datum
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (q : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m
      (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q).val=
    ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q) χ Q m := rfl


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_selected_original_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_selected_original_datum
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_selected_original_ordinary_datum

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainSelectedRowEmbedding -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighNormalizedPayment; sha256 e07ac82161de238588b64d3ee7eb325b874b40b4f6ea645c87ccd4b584fd2473 -/
section
                                                                    
                                                           
                                                             

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
local instance geometryMainHighNormalizedPaymentSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := mainOrdinaryFiberSumDecidable

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource


open Cycle61FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle61Moment.LowBranch

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The selected first allocation has the actual ordinary joint-key fiber
budget. The first-label/projector injection replaces every label count. -/
theorem eventually_actual_selected_main_ordinary_fibers (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0< K),
      Squarefree seed → Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → K≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed K Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected K (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      ∀(χ₀ : Index→ RayCharacter)(Q : Index→ Ideal O)(m : Index→ O),
      let ordinary:=fun q=>ordinarySecondDatum (datum q) (χ₀ q) (Q q) (m q)
      ∀(rows : Finset (secondLiveRows (fun q=>(ordinary q).block))),
      (∀r∈rows,(datum r.val.1).block.value ballProfile≠0) →
      ∀second : Bool,
      let ho : ∀r : secondLiveRows (fun q=>(ordinary q).block),
        jointFirstFrequency left u₀ unit (secondEncodedRow (fun q=>(ordinary q).block) label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit
          (secondEncodedRow (fun q=>(ordinary q).block) label r) hu₀ (hunit _)
          (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      let key := fun r : rows=>secondEncodedNonzeroRow (fun q=>(ordinary q).block) label r.val left u₀ unit (ho r.val)
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : rows=>
        (if second then reflectedNonzeroJointLabel (key r) else key r)=target)).card:ℝ)≤ D*Z^(2*ε) := by
  let receipt:=actual_geometry_main_ordinary_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  let D:=Classical.choose receipt
  have hD:= (Classical.choose_spec receipt).1
  have hevent:=(Classical.choose_spec receipt).2
  refine ⟨D,hD,?_⟩
  filter_upwards [hevent] with Z he
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard hend hV hKM
    hs₁ hs₂ ha hr bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum label left unit hunit χ₀ Q m ordinary
    rows hn second ho key target
  let block:=fun q : Index=>(datum q).block
  let fullRows : ∀q,(datum q).rows=sourceRows (datum q).C (datum q).D (datum q).inactive (datum q).radius:=fun _=>rfl
  let embed:=ordinaryHighOriginalRow datum χ₀ Q m fullRows
  let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0:=
    fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
      hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
  have hb:=he hZ reflected s R seed K a reserve t hK hseed hcard hend hV hKM hs₁ hs₂ ha hr
    bin column hinj alloc halloc χ₀ Q m rows hn second target
  have hkey (r : rows) :
      secondEncodedNonzeroRow block label (embed r.val) left u₀ unit (hf (embed r.val))=key r :=
    ordinary_main_nonzero_key_eq datum χ₀ Q m fullRows label left u₀ unit r.val
      (hf (embed r.val)) (ho r.val)
  let oldKey:=fun r : rows=>secondEncodedNonzeroRow block label (embed r.val) left u₀ unit (hf (embed r.val))
  change ((Finset.univ.filter (fun r : rows=>
    (if second then reflectedNonzeroJointLabel (oldKey r) else oldKey r)=target)).card:ℝ)≤ D*Z^(2*ε) at hb
  have heq : oldKey=key:=funext hkey
  rw [heq] at hb
  exact hb

/-- The literal first-child height and both signed Mellin orientations
satisfy the high window gates on the small combined-height range. -/
theorem actual_selected_main_high_shifted_heights
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(s : Input α)(R seed : Ideal O)
    (Z D amp ξ reserve b baseHeight : ℝ)(N : ℕ)(hZ : 1< Z)
    (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
    (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (q : (l : Label)×GeometryLowSecondIndex reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin (firstIndex l))
    (freq : α→ℝ)(height t₀ u T e : ℝ)(p : BufferIndex e)
    (hT : 0≤ T)(hh : 0≤ height)(hf : ∀j,|freq j|≤ height)(hp : 1≤ p.1.val)
    (hsmall : 2*(1+|baseHeight|+height+2*Real.pi*(|t₀|+|u|))≤ T) :
    let d:=geometryLowSecondDatum reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin
      (firstIndex q.1) hs₁ hs₂ q.2
    let shifted:=d.input.t+2*Real.pi*(u-(if second then -t₀ else t₀))
    (∀j,|shifted+freq j|+T/2≤(3*p.1.val+2:ℕ)*T) ∧
      |shifted|+T/2≤(3*p.1.val+2:ℕ)*T := by
  intro d shifted
  have hs:=main_low_payment_shifted_height_envelope second baseHeight height t₀ u T hT hsmall
  have hb:=main_low_payment_height_bin p hp
    (baseHeight+2*Real.pi*(u-(if second then -t₀ else t₀))) height T hT hs
  have hshift : shifted=baseHeight+2*Real.pi*(u-(if second then -t₀ else t₀)):=rfl
  rw [←hshift] at hb
  refine ⟨?_,?_⟩
  · intro j
    have ha:=abs_add_le shifted (freq j)
    linarith [hf j]
  · linarith



section RowTransport
variable {α Selected Original : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Selected] [Fintype Original]
variable (datum : Original→ SecondInputDatum α)(embed : Selected→ Original)

def highSelectedRowEmbedding
    (r : SecondRow (fun j=>(datum (embed j)).block)) : SecondRow (fun j=>(datum j).block) :=
  ⟨embed r.1,r.2⟩

omit [Fintype Selected] [Fintype Original] in
theorem high_selected_row_embedding_injective (hinj : Function.Injective embed) :
    Function.Injective (highSelectedRowEmbedding datum embed) := by
  intro r v h
  have hl : r.1=v.1:=hinj (congrArg Sigma.fst h)
  apply Sigma.ext hl
  exact (Sigma.mk.inj_iff.mp h).2

theorem high_selected_row_embedding_live
    (r : SecondRow (fun j=>(datum (embed j)).block)) :
    highSelectedRowEmbedding datum embed r∈secondLiveRows (fun j=>(datum j).block) ↔
      r∈secondLiveRows (fun j=>(datum (embed j)).block) := by
  simp only [secondLiveRows,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl


def highSelectedLiveRowEmbedding
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) : secondLiveRows (fun j=>(datum j).block) :=
  ⟨highSelectedRowEmbedding datum embed r.val,(high_selected_row_embedding_live datum embed r.val).mpr r.property⟩

theorem high_selected_live_encoded_row (first : Original→ FirstSourceLabel)
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    secondEncodedRow (fun j=>(datum j).block) first (highSelectedLiveRowEmbedding datum embed r)=
      secondEncodedRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r := rfl

theorem high_selected_live_nonzero_key (first : Original→ FirstSourceLabel)
    (r : secondLiveRows (fun j=>(datum (embed j)).block))
    (left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
    (hOriginal : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum j).block) first (highSelectedLiveRowEmbedding datum embed r))≠0)
    (hSelected : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r)≠0) :
    secondEncodedNonzeroRow (fun j=>(datum j).block) first (highSelectedLiveRowEmbedding datum embed r) left u₀ unit hOriginal=
      secondEncodedNonzeroRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r left u₀ unit hSelected := rfl

omit [Fintype Selected] in
/-- The projector union belongs to the original family, before any row or
zero-bin selection. -/
theorem high_selected_original_projector_union
    (r : SecondRow (fun j=>(datum (embed j)).block)) :
    secondResidualIdeals (fun j=>(datum (embed j)).block) r⊆mainHighProjectorUnion datum :=
  main_high_residual_subset_union datum (highSelectedRowEmbedding datum embed r)

omit [Fintype Selected] [Fintype Original] in
theorem high_selected_row_cost_image [DecidableEq (SecondRow (fun j=>(datum j).block))]
    (hinj : Function.Injective embed)
    (N : ℕ)(a ap : ℝ)(second : Bool)(coefficient : Original→ℝ)(t u : ℝ)
    (rows : Finset (SecondRow (fun j=>(datum (embed j)).block))) :
    (∑r∈rows,∑L∈secondResidualIdeals (fun j=>(datum (embed j)).block) r,
      mainNormalizedPhysicalCost N a ap second (fun j=>datum (embed j)) (fun j=>coefficient (embed j)) t u r L)=
    ∑r∈rows.image (highSelectedRowEmbedding datum embed),
      ∑L∈secondResidualIdeals (fun j=>(datum j).block) r,
      mainNormalizedPhysicalCost N a ap second datum coefficient t u r L := by
  rw [Finset.sum_image]
  · rfl
  · exact fun r _ v _ h=>high_selected_row_embedding_injective datum embed hinj h
end RowTransport

section SelectedTransport
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance geometryMainHighNormalizedSelectedSumDecidable : DecidableEq (α⊕Fin 2) := geometryMainNormalizedSumDecidable
variable (reflected : Bool)(s : Input α)(R seed : Ideal O)
variable (Z D amp ξ reserve b baseHeight : ℝ)(N : ℕ)(hZ : 1< Z)
variable (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
variable (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
local notation "Original" => {j : GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin // j∈geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂}
local notation "Selected" => mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ firstIndex
local notation "embed" => mainLowSelectedOriginal reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ firstIndex

/-- Exact transport of the selected first-allocation family into the original
ordinary family. The coefficient includes physical mass and child volume. -/
theorem actual_selected_main_high_cost_image
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val)))
    (a ap : ℝ)(second : Bool)(t u : ℝ) :
    let raw : Original→ GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin:=Subtype.val
    ∀(χ : Original→ RayCharacter)(Q : Original→ Ideal O)(m : Original→ O)(mass : Original→ℝ),
    let datum:=fun j : Original=>geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ (χ j) (Q j) (m j) (raw j)
    let coefficient:=fun j : Original=>mass j/volume (datum j).input
    ∀rows : Finset (SecondRow (fun j : Selected=>(datum (embed j)).block)),
    (∑r∈rows,∑L∈secondResidualIdeals (fun j : Selected=>(datum (embed j)).block) r,
      mainNormalizedPhysicalCost N a ap second (fun j : Selected=>datum (embed j)) (fun j=>coefficient (embed j)) t u r L)=
    ∑r∈rows.image (highSelectedRowEmbedding datum embed),
      ∑L∈secondResidualIdeals (fun j=>(datum j).block) r,
      mainNormalizedPhysicalCost N a ap second datum coefficient t u r L := by
  intro raw χ Q m mass datum coefficient rows
  exact high_selected_row_cost_image datum embed
    (main_low_selected_original_injective reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ firstIndex hinj)
    N a ap second coefficient t u rows
end SelectedTransport

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_actual_selected_main_ordinary_fibers

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_main_high_shifted_heights

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_selected_row_embedding_injective

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_selected_row_embedding_live

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_selected_row_cost_image

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_main_high_cost_image

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_selected_live_encoded_row

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_selected_live_nonzero_key

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_selected_original_projector_union

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighNormalizedPayment -/
