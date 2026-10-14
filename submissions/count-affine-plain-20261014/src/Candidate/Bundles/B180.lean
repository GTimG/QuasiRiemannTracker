/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B135
import Candidate.Bundles.B166
import Candidate.Bundles.B170
import Candidate.Bundles.B171
import Candidate.Bundles.B178
import Candidate.Bundles.B179
import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighQuantitativePayment; sha256 03bceb775a486ce5c08d7174b5d339a607b32442ab9c9262477e890255bccbc9 -/
section
                                                                     
                                                                    
                                                             
                                                                      

set_option autoImplicit false
set_option maxHeartbeats 12000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentSecondEnergySplit CenteredMomentWholeDivisorShell
open CenteredMomentSourceRow CenteredMomentCommonPairedSource CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstSourceReduction
local notation "O" => HeckeFamily.O
local instance geometryMainHighQuantitativeSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable


section CanonicalPartition
open RayFourExpansion ConcretePrimeRowBridge CenteredMomentSourceMass Cycle61Moment.LowBranch
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The high row keeps the low partition's literal buffered choice when
its actual retained state is widened. -/
theorem actual_main_high_canonical_row_admission
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask bΦ : ℝ) (hZ : 1< Z) (hbΦ : 2≤ bΦ) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (z : mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)) :
    let base : NaturalState Z Bmask 2 :=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let st:=widenHighState base bΦ hbΦ
    let keep:=(actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
      Z Bmask hZ second hP hPN (fun _=>True) z.val z.property).1
    1≤(st.radial.profile (normValue z.val/st.radial.scale)).re ∧
    st.radial.profile (normValue z.val/st.radial.scale)≠0 ∧ z.val≠0 ∧
    GeometryZeroBin M H hH st η₀ hQM hQη z.val keep e T
      (mainLowCanonicalSelector M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
        hP hPN η₀ hQM hQη e T he hT hβlo hβhi z) := by
  intro base st keep
  have ha:=actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  have hw : 1≤(st.radial.profile (normValue z.val/st.radial.scale)).re:=ha.2.2
  have hn : st.radial.profile (normValue z.val/st.radial.scale)≠0:=by
    intro h; rw [h] at hw; norm_num at hw
  have hb:=actual_main_low_canonical_zero_bin M H hH d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN η₀ hQM hQη e T he hT hβlo hβhi z
  exact ⟨hw,hn,st.row_ne_zero _ keep,
    main_high_widen_zero_bin M H hH base bΦ hbΦ η₀ hQM hQη z.val keep e T _ hb⟩

/-- Every ordinary live row uses the literal shared selector before any shell restriction. -/
theorem actual_main_high_canonical_family_admission
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α) (χ₀ : Label→ RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask bΦ : ℝ) (hZ : 1< Z) (hbΦ : 2≤ bΦ) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
    let rows:=secondLiveRows (fun l=>(ordinary l).block)
    let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
    let base:=fun r : rows=>retainedState Z Bmask hZ
      (if second then (d r.val.1).τ r.val.2.2.1⁻¹ else (d r.val.1).τ r.val.2.1) Q
      ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
      (hP r.val.1) (hPN r.val.1)
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let st:=fun r=>widenHighState (base r) bΦ hbΦ
    let select:=mainLowFamilyCanonicalSelector M H hH d χ₀ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi
    ∃keep : ∀r : rows,(st r).radial.keep (signed r),∀r : rows,
      1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
      (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0 ∧ signed r≠0 ∧
      GeometryZeroBin M H hH (st r) η₀ hQM hQη (signed r) (keep r) e T (select r) := by
  intro ordinary rows signed base st select
  let sourceRow : (r : rows)→ mainLowSourceRows second (ordinary r.val.1) (fun _=>True) := fun r=>
    (⟨signed r,by
      apply (mem_main_low_source_rows second (ordinary r.val.1) (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩ :
      mainLowSourceRows second (ordinary r.val.1) (fun _=>True))
  obtain ⟨keep,oldSelect,hold⟩ := actual_main_high_widened_selector M H hH d χ₀ Q hQ m hm hml hm2
    Z Bmask bΦ hZ hbΦ second hP hPN η₀ hQM hQη e T he hT hβlo hβhi
  refine ⟨keep,?_⟩
  intro r
  have hg := actual_main_high_canonical_row_admission M H hH (d r.val.1) (χ₀ r.val.1)
    r.val.2.1 r.val.2.2.1 Q hQ m hm hml hm2 Z Bmask bΦ hZ hbΦ second
    (hP r.val.1) (hPN r.val.1) η₀ hQM hQη e T he hT hβlo hβhi (sourceRow r)
  exact ⟨(hold r).1,(hold r).2.1,(hold r).2.2.1,hg.2.2.2⟩

end CanonicalPartition

/-- Keep the ordinary row carrier opaque while the physical family is instantiated. -/
def geometryOrdinaryHighRowCost
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→ SecondInputDatum α)
    (χ : Label→ RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(datum l).rows=sourceRows (datum l).C (datum l).D (datum l).inactive (datum l).radius)
    (second : Bool)
    (weight height : secondLiveRows (fun l=>(datum l).block)→ℝ)
    (Ds : secondLiveRows (fun l=>(datum l).block)→ Finset (Ideal O))
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (datum l) (χ l) (Q l) (m l)).block)) : ℝ :=
  weight (ordinaryHighOriginalRow datum χ Q m hrows r)*
    highNormalizedRowCost second (fun l=>ordinarySecondDatum (datum l) (χ l) (Q l) (m l)) r
      (height (ordinaryHighOriginalRow datum χ Q m hrows r))
      (Ds (ordinaryHighOriginalRow datum χ Q m hrows r))

theorem geometry_ordinary_high_row_cost_image
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (datum : Label→ SecondInputDatum α)
    (χ : Label→ RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(datum l).rows=sourceRows (datum l).C (datum l).D (datum l).inactive (datum l).radius)
    (rows : Finset (secondLiveRows (fun l=>(ordinarySecondDatum (datum l) (χ l) (Q l) (m l)).block)))
    (second : Bool)
    (weight height : secondLiveRows (fun l=>(datum l).block)→ℝ)
    (Ds : secondLiveRows (fun l=>(datum l).block)→ Finset (Ideal O)) :
    (∑r∈rows,geometryOrdinaryHighRowCost datum χ Q m hrows second weight height Ds r)=
      ∑r∈rows.image (ordinaryHighOriginalRow datum χ Q m hrows),
        weight r*highNormalizedRowCost second datum r (height r) (Ds r) :=
  geometry_ordinary_high_image_sum datum χ Q m hrows rows second weight height Ds


private theorem geometry_high_coarse_sum_association {ι : Type*} (rows : Finset ι)
    {m k n l q : rows→ℝ} {A : ℝ}
    (h : (∑r : rows,m r*(k r*n r/l r)*q r)≤ A) :
    (∑r : rows,m r*k r*n r/l r*q r)≤ A := by
  convert h using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The all-projector source estimate retains the first physical mass and
restores its side factor only in the coarse exponent. -/
def MainHighCoarseSideSpec {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U exponent K Z : ℝ) : Prop :=
    ∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |Dfirst|≤ B →
      |a|≤ B → |frequencyLoss Z 32 ξ+reserve|≤ B → (∀j,s.M j≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^plainCap) →
      (∀j,s.P j≤ Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum : Index→ SecondInputDatum α := fun q=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset (secondLiveRows (fun q=>(datum q).block)))(second : Bool)(W : 𝓢(ℝ,ℂ))
        (height : rows→ℝ)(Ds : rows→ Finset (Ideal O))(control B₁ B₂ : ℝ),
      0≤ control → 0≤ B₁ → 0≤ B₂ →
      (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex r.val.val.1.1).1.val *
        (firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
          (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex r.val.val.1.1).1.val)/
          volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
          (firstIndex r.val.val.1.1)))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap*
        highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤ K*control*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^exponent

theorem actual_main_high_original_coarse_side_payment {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ plainCap)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤ loss)(hU : 0≤ U) :
    ∃K : ℝ,0< K ∧ ∀ᶠ Z : ℝ in atTop,
      MainHighCoarseSideSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U
        (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z := by
  let coarse : ℝ := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε
  let Cside : ℝ := geometrySupportConstant N lo ap ap
  have hside : 0< Cside := geometrySupportConstant_pos N lo ap ap hlo hap hap
  let receipt := actual_geometry_main_all_projector_coarse_family
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  let Kc := Classical.choose receipt
  have hKc := (Classical.choose_spec receipt).1
  have hcoarse := (Classical.choose_spec receipt).2
  refine ⟨Kc*(1+Cside⁻¹^2),by positivity,?_⟩
  filter_upwards [hcoarse] with Z hc
  unfold MainHighCoarseSideSpec
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    rows second W height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs cost
  classical
  have hraw := hc hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin (fun l=>(firstIndex l).1) hinj (fun l=>(firstIndex l).2) halloc
    rows second W height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs
  have hraw' := geometry_high_coarse_sum_association rows hraw
  by_cases hr : rows.Nonempty
  · obtain ⟨r,hr⟩ := hr
    have hunit := actual_geometry_coarse_side_unit reflected Cside hside s R seed
      (Z^Dfirst) Z ξ B hZ.le hB hseed hs₁ hs₂ hsource bin (firstIndex r.val.1.1).1.val.1
    exact geometry_coarse_side_bound reflected Cside Z B coarse _ Kc control bin
      (zero_lt_one.trans hZ) hKc.le hcontrol hunit hraw'
  · have hzero : (∑r : rows,cost r)=0 := by
      apply Finset.sum_eq_zero
      intro r _
      exact False.elim (hr ⟨r.val,r.property⟩)
    rw [hzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hcontrol)
      (geometry_high_factor_pos reflected Cside bin hside).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_canonical_row_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_ordinary_high_row_cost_image
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_original_coarse_side_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_canonical_family_admission

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighQuantitativePayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowPhysicalPayment; sha256 d79b1362343230b98040f1308438382545303f26766fa20037bb0fa68f2b2856 -/
section
                                                                      
                                                                    
                                                       
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowPhysicalDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


theorem mainLowPhysicalSupported (second : Bool) (d : SecondInputDatum α) :
    Supported (if second then d.D else d.C) := by
  cases second
  · exact d.hC
  · exact d.hD

/-- Extend the literal selector only to express an ordinary finite-set
filter. No unsupported row receives a buffered-bin certificate. -/
def mainLowPhysicalSourcePredicate (rows : Finset O) {e : ℝ}
    (select : rows→ BufferIndex e) (z : O) : Prop :=
  if hz : z∈rows then bufferValue e (select ⟨z,hz⟩)<167/200 else False

theorem main_low_physical_source_sum (second : Bool) (d : SecondInputDatum α)
    {e : ℝ} (select : mainLowSourceRows second d (fun _=>True)→ BufferIndex e)
    (f : O→ℝ) :
    (∑z∈mainLowSourceRows second d
      (mainLowPhysicalSourcePredicate (mainLowSourceRows second d (fun _=>True)) select),f z)=
    ∑z : mainLowSourceRows second d (fun _=>True),
      if bufferValue e (select z)<167/200 then f z.val else 0 := by
  let rows:=mainLowSourceRows second d (fun _=>True)
  have heq : mainLowSourceRows second d (mainLowPhysicalSourcePredicate rows select)=
      rows.filter (mainLowPhysicalSourcePredicate rows select) := by
    ext z
    simp only [Finset.mem_filter]
    change (_ ↔ z∈mainLowSourceRows second d (fun _=>True) ∧ _)
    simp only [mem_main_low_source_rows]
    constructor
    · rintro ⟨x,hx,he,hl⟩
      exact ⟨⟨x,hx,he,True.intro⟩,hl⟩
    · rintro ⟨⟨x,hx,he,_⟩,hl⟩
      exact ⟨x,hx,he,hl⟩
  rw [heq,Finset.sum_filter]
  change (∑z∈rows,if mainLowPhysicalSourcePredicate rows select z then f z else 0)=_
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z _
  simp only [mainLowPhysicalSourcePredicate,dite_eq_left z.property]

/-- The complete fixed-ray physical low cost. The original block label
may already carry its full-nonzero filter; restriction never tests a new
ordinary-block norm. Both actual rays and signed source rows are retained. -/
def mainLowPhysicalCompleteCost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) : ℝ :=
  ∑r∈secondLiveRows (fun l=>(d l).block),
    ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
      if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d r.1) (fun _=>True))
          (select r.1 r.2.1 r.2.2.1) (mainLowSignedRow second r.2.2.2.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u r D else 0

/-- Exact source-to-physical transport. The physical lower factor is
outside the complete source sum; no child volume or normalizer is lost. -/
theorem actual_main_low_complete_physical_reindex {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select=
      (1/lowerFactor N a ap)*
      ∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        mainLowCompleteSelectedCost
          (fun l=>mainLowSourceRows second (d l) (fun _=>True))
          (fun l=>select l χ ψ) (fun l=>(d l).block.divisors.filter Squarefree)
          (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
          (fun l D z=>‖normalizedColumn
            (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
              ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (mainLowPhysicalSupported second (d l))
            (d l).R (d l).seed D z‖^2) := by
  unfold mainLowPhysicalCompleteCost
  rw [actual_main_low_physical_cost_reindex N a ap second d coefficient t u
    (fun l χ ψ=>mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True)) (select l χ ψ))]
  have hsources : ∀l χ ψ D,
      (∑z∈mainLowSourceRows second (d l)
        (mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l χ ψ)),
        ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported second (d l))
          (d l).R (d l).seed D z‖^2)=
      ∑z : mainLowSourceRows second (d l) (fun _=>True),
        if bufferValue e (select l χ ψ z)<167/200 then
          ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
            ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (mainLowPhysicalSupported second (d l))
            (d l).R (d l).seed D z.val‖^2 else 0 := by
    intro l χ ψ D
    exact main_low_physical_source_sum second (d l) (select l χ ψ) _
  simp_rw [hsources]
  rw [←Finset.sum_comm]
  apply congrArg (fun x=>x) -- stage the second ray before the label sum
  calc
    _=∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        ∑l,∑D∈(d l).block.divisors.filter Squarefree,
          (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
          (∑z : mainLowSourceRows second (d l) (fun _=>True),
            if bufferValue e (select l χ ψ z)<167/200 then
              ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
                (if second then (d l).D else (d l).C)
                (mainLowPhysicalSupported second (d l))
                (d l).R (d l).seed D z.val‖^2 else 0) := by
      apply Finset.sum_congr rfl
      intro χ _
      exact Finset.sum_comm
    _=_ := by
      unfold mainLowCompleteSelectedCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      ring

/-- Fixed rays and a complete original live column, before any frequency
choice. This is the literal physical summand used by the buffered partition. -/
def mainLowFixedRayPhysicalCost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→ mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) : ℝ :=
  ∑l,∑D∈(d l).block.divisors.filter Squarefree,
    ∑z∈secondLiveColumnRows (d l).block,
      if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u ⟨l,χ,ψ,z⟩ D else 0

theorem actual_main_low_fixed_ray_physical_reindex {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→ mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select=
      (1/lowerFactor N a ap)*mainLowCompleteSelectedCost
        (fun l=>mainLowSourceRows second (d l) (fun _=>True)) select
        (fun l=>(d l).block.divisors.filter Squarefree)
        (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
        (fun l D z=>‖normalizedColumn
          (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
            ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported second (d l))
          (d l).R (d l).seed D z‖^2) := by
  unfold mainLowFixedRayPhysicalCost mainLowCompleteSelectedCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  have hfactor : ∀z,
      (if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u ⟨l,χ,ψ,z⟩ D else 0)=
      (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
      (if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported second (d l))
          (d l).R (d l).seed D (mainLowSignedRow second z.val)‖^2 else 0) := by
    intro z
    cases second <;> simp only [mainNormalizedPhysicalCost,mainLowSignedRow,ite_true]
    all_goals split_ifs <;> simp only [mul_zero]
  simp_rw [hfactor]
  rw [←Finset.mul_sum,main_low_source_sum second (d l)
    (mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True)) (select l))
    (fun z=>‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
      ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
      (if second then (d l).D else (d l).C)
      (mainLowPhysicalSupported second (d l)) (d l).R (d l).seed D z‖^2),
    main_low_physical_source_sum]
  ring

/-- Fixed ray cardinalities are paid once after complete source columns.
The supplied source estimate is the quantitative receipt's literal last
inequality, not a norm estimate for an arithmetic label. -/
theorem main_low_physical_fixed_ray_sum_le {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e)
    (bound : ℝ) (hlower : 0< lowerFactor N a ap)
    (hsource : ∀χ ψ,mainLowCompleteSelectedCost
      (fun l=>mainLowSourceRows second (d l) (fun _=>True)) (fun l=>select l χ ψ)
      (fun l=>(d l).block.divisors.filter Squarefree)
      (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
      (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported second (d l))
        (d l).R (d l).seed D z‖^2)≤ bound) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select≤
      (1/lowerFactor N a ap)*(Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*bound := by
  rw [actual_main_low_complete_physical_reindex]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun χ _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun ψ _=>hsource χ ψ))
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0≤1/lowerFactor N a ap)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc] using h'

private theorem fixed_ray_source_transport {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→ mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e)
    (c : Label→ Ideal O→ℝ) (value : Label→ Ideal O→ O→ℝ) (bound : ℝ)
    (hlower : 0< lowerFactor N a ap)
    (hc : ∀l D,coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive=c l D)
    (hv : ∀l D z,‖normalizedColumn
      (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
        ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
      (if second then (d l).D else (d l).C)
      (mainLowPhysicalSupported second (d l))
      (d l).R (d l).seed D z‖^2=value l D z)
    (hb : mainLowCompleteSelectedCost (fun l=>mainLowSourceRows second (d l) (fun _=>True))
      select (fun l=>(d l).block.divisors.filter Squarefree) c value≤ bound) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select≤
      (1/lowerFactor N a ap)*bound := by
  rw [actual_main_low_fixed_ray_physical_reindex]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤1/lowerFactor N a ap)
  have heq : mainLowCompleteSelectedCost (fun l=>mainLowSourceRows second (d l) (fun _=>True))
      select (fun l=>(d l).block.divisors.filter Squarefree)
      (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
      (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported second (d l))
        (d l).R (d l).seed D z‖^2)=
      mainLowCompleteSelectedCost (fun l=>mainLowSourceRows second (d l) (fun _=>True))
        select (fun l=>(d l).block.divisors.filter Squarefree) c value := by
    have hceq : (fun l (_ : Ideal O)=>coefficient l*(d l).K*
        normalizer (d l).C (d l).D (d l).inactive)=c := by
      funext l D
      exact hc l D
    have hveq : (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported second (d l))
        (d l).R (d l).seed D z‖^2)=value := by
      funext l D z
      exact hv l D z
    rw [hceq,hveq]
  exact heq ▸ hb

attribute [local irreducible] mainLowFixedRayPhysicalCost mainLowCompleteSelectedCost
  selectedFirstProjectors

/-- A complete original-nonzero second family may be stored separately
under each chosen first column. This exact sigma identity preserves that
subtype, its common allocation and its literal signed frequency set. -/
theorem main_low_fixed_ray_sigma {Label : Type*} [Fintype Label]
    (Block : Label→ Type*) [∀l,Fintype (Block l)]
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : ((l : Label)×Block l)→ SecondInputDatum α)
    (coefficient : ((l : Label)×Block l)→ℝ) (t u : ℝ)
    (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (r : (l : Label)×Block l)→ mainLowSourceRows second (d r) (fun _=>True)→ BufferIndex e) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select=
      ∑l,mainLowFixedRayPhysicalCost N a ap second
        (fun r : Block l=>d ⟨l,r⟩) (fun r=>coefficient ⟨l,r⟩) t u χ ψ
        (fun r=>select ⟨l,r⟩) := by
  unfold mainLowFixedRayPhysicalCost
  exact Fintype.sum_sigma _

set_option maxHeartbeats 320000 in
/-- The first projector union is taken on the selected original columns
before the complete second family, fixed rays or buffered bins are split.
No block or arithmetic-label cardinality appears. -/
theorem main_low_physical_first_shell_reindex {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource}
    (column : Label→ FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : Label→ Type*) [∀l,Fintype (Block l)]
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : ((l : Label)×Block l)→ SecondInputDatum α)
    (coefficient : ((l : Label)×Block l)→ℝ) (t u : ℝ)
    (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (r : (l : Label)×Block l)→ mainLowSourceRows second (d r) (fun _=>True)→ BufferIndex e) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select=
      ∑n∈CenteredMomentWholeDivisorShell.selectedShells (selectedFirstProjectors column),
        mainLowFixedRayPhysicalCost N a ap second
          (fun r : (l : SelectedFirstShell column n)×Block l.val=>d ⟨r.1.val,r.2⟩)
          (fun r=>coefficient ⟨r.1.val,r.2⟩) t u χ ψ
          (fun r=>select ⟨r.1.val,r.2⟩) := by
  rw [main_low_fixed_ray_sigma,selected_first_shell_sum column hs]
  apply Finset.sum_congr rfl
  intro n _
  exact (main_low_fixed_ray_sigma (fun l : SelectedFirstShell column n=>Block l.val)
    N a ap second (fun r=>d ⟨r.1.val,r.2⟩) (fun r=>coefficient ⟨r.1.val,r.2⟩)
    t u χ ψ (fun r=>select ⟨r.1.val,r.2⟩)).symm

/-- All fixed rays share the same first projector union. A shell payment
therefore incurs its norm-dyad count once, after both ray sums. -/
theorem main_low_physical_complete_ray_sum {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select=
      ∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ
          (fun l=>select l χ ψ) := by
  rw [actual_main_low_complete_physical_reindex,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  exact (actual_main_low_fixed_ray_physical_reindex N a ap second d coefficient t u χ ψ _).symm

/-- Pure payment contraction on the actual nested physical family. The
per-shell source estimate is supplied by `actual_main_low_physical_bins`;
this step charges only the common first-projector shells and fixed rays. -/
theorem main_low_physical_first_shell_payment {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource}
    (column : Label→ FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : Label→ Type*) [∀l,Fintype (Block l)]
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : ((l : Label)×Block l)→ SecondInputDatum α)
    (coefficient : ((l : Label)×Block l)→ℝ) (t u : ℝ) {e : ℝ}
    (select : (r : (l : Label)×Block l)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d r) (fun _=>True)→ BufferIndex e)
    (bound C Z ε : ℝ) (hbound : 0≤ bound)
    (hcard : ((CenteredMomentWholeDivisorShell.selectedShells
      (selectedFirstProjectors column)).card:ℝ)≤ C*Z^ε)
    (hpay : ∀n∈CenteredMomentWholeDivisorShell.selectedShells (selectedFirstProjectors column),
      ∀χ ψ,mainLowFixedRayPhysicalCost N a ap second
        (fun r : (l : SelectedFirstShell column n)×Block l.val=>d ⟨r.1.val,r.2⟩)
        (fun r=>coefficient ⟨r.1.val,r.2⟩) t u χ ψ
        (fun r=>select ⟨r.1.val,r.2⟩ χ ψ)≤ bound) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select≤
      (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(C*Z^ε*bound) := by
  rw [main_low_physical_complete_ray_sum]
  have hray (χ ψ : RayFourExpansion.RayCharacter) :
      mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ
        (fun l=>select l χ ψ)≤ C*Z^ε*bound := by
    rw [main_low_physical_first_shell_reindex column hs Block]
    calc
      _≤∑_n∈CenteredMomentWholeDivisorShell.selectedShells (selectedFirstProjectors column),bound :=
        Finset.sum_le_sum (fun n hn=>hpay n hn χ ψ)
      _≤ C*Z^ε*bound := by
        simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hcard hbound
  calc
    _≤∑_χ : RayFourExpansion.RayCharacter,∑_ψ : RayFourExpansion.RayCharacter,C*Z^ε*bound :=
      Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ψ _=>hray χ ψ))
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc]

/-- Original stored-pool caps pay the common FIRST projector shells
uniformly before all selected labels, original-nonzero second blocks and
Mellin shifts. The supplied shell receipt is the literal physical-bin
continuation, not a cardinality bound on arithmetic labels. -/
theorem eventual_actual_main_low_physical_first_shell_contraction
    (N : ℕ) (U εshell : ℝ) (hU : 0≤ U) (hεshell : 0<εshell) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι Label : Type*}[Fintype ι][DecidableEq ι][Fintype Label]
        (s : Input ι),Fintype.card ι≤ N →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
        (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (_hs : ∀l,Squarefree (column l).2.1.val)
        (Block : Label→ Type*)[∀l,Fintype (Block l)]
        (a ap : ℝ)(second : Bool)
        (d : ((l : Label)×Block l)→ SecondInputDatum ι)
        (coefficient : ((l : Label)×Block l)→ℝ)(t u e bound : ℝ)
        (select : (r : (l : Label)×Block l)→(χ ψ : RayFourExpansion.RayCharacter)→
          mainLowSourceRows second (d r) (fun _=>True)→ BufferIndex e),
      0≤ bound →
      (∀n∈selectedShells (selectedFirstProjectors column),∀χ ψ,
        mainLowFixedRayPhysicalCost N a ap second
          (fun r : (l : SelectedFirstShell column n)×Block l.val=>d ⟨r.1.val,r.2⟩)
          (fun r=>coefficient ⟨r.1.val,r.2⟩) t u χ ψ
          (fun r=>select ⟨r.1.val,r.2⟩ χ ψ)≤ bound) →
      mainLowPhysicalCompleteCost N a ap second d coefficient t u select≤
        (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(C*Z^εshell*bound) := by
  obtain ⟨C,hC,hcount⟩:=eventual_actual_geometry_selected_first_shell_subpower N U εshell hU hεshell
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι Label _ _ _ s hN hpool R seed K ξ hK bin column hs Block _ a ap second
    d coefficient t u e bound select hbound hpay
  exact main_low_physical_first_shell_payment column hs Block N a ap second d coefficient t u
    select bound C Z εshell hbound (hz.2 s hN hpool R seed K ξ hK bin column) hpay

/-- The complete ordinary low subset, before any projector grouping.
The row's block label is unchanged, including its original-nonzero subtype. -/
def mainLowPhysicalOrdinaryRows {Label : Type*} [Fintype Label]
    (second : Bool) (d : Label→ SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    Finset (secondLiveRows (fun l=>(d l).block)) :=
  Finset.univ.filter (fun r=>mainLowPhysicalSourcePredicate
    (mainLowSourceRows second (d r.val.1) (fun _=>True))
    (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val))

/-- The exact physical cost is the normalized row family consumed by the
all-height splice. The height retains both signed Mellin shifts. -/
theorem actual_main_low_physical_ordinary_row_cost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select=
      ∑r∈mainLowPhysicalOrdinaryRows second d select,
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  unfold mainLowPhysicalCompleteCost mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro r _
  rw [actual_second_residual_ideals_label]
  by_cases hp : mainLowPhysicalSourcePredicate
      (mainLowSourceRows second (d r.val.1) (fun _=>True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val)
  · simp only [hp,ite_true]
    cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

private theorem ordinary_physical_divisors (d : SecondInputDatum α)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O) :
    (ordinarySecondDatum d χ Q m).block.divisors=d.block.divisors := rfl

set_option maxHeartbeats 320000 in
/-- Ordinary low rows are transported to the original source family
before the genuine coarse theorem. The original label/ray/frequency image
is injective; an ordinary block need not be nonzero. -/
theorem actual_main_low_physical_original_row_cost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (χ₀ : Label→ RayFourExpansion.RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows
      (d l).C (d l).D (d l).inactive (d l).radius)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l))
        (fun _=>True)→ BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second
      (fun l=>ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l)) coefficient t u select=
      ∑r∈(mainLowPhysicalOrdinaryRows second
        (fun l=>ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l)) select).image
          (ordinaryHighOriginalRow d χ₀ Q m hrows),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_ordinary_row_cost]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r _
    rw [ordinary_high_original_row_cost]
    have hlabel : (ordinaryHighOriginalRow d χ₀ Q m hrows r).val.1=r.val.1 := rfl
    rw [hlabel]
    have hdiv:=ordinary_physical_divisors (d r.val.1) (χ₀ r.val.1) (Q r.val.1) (m r.val.1)
    rw [hdiv]
    congr 1
  · intro r _ z _ heq
    exact ordinary_high_original_row_injective d χ₀ Q m hrows heq

/-- Inclusion of a selected original block-label family into the full
second family. Both rays and the literal frequency are unchanged. -/
def mainLowOriginalLabelRow {Label Original : Type*} [Fintype Label] [Fintype Original]
    (embed : Label→ Original) (d : Original→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d (embed l)).block)) :
    secondLiveRows (fun l=>(d l).block) := by
  refine ⟨⟨embed r.val.1,r.val.2⟩,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩

theorem main_low_original_label_row_injective {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→ Original) (hinj : Function.Injective embed)
    (d : Original→ SecondInputDatum α) :
    Function.Injective (mainLowOriginalLabelRow embed d) := by
  intro r s h
  have hl : r.val.1=s.val.1 := hinj (congrArg (fun q=>q.val.1) h)
  rcases r with ⟨⟨l,χr,ψr,zr⟩,hr⟩
  rcases s with ⟨⟨k,χs,ψs,zs⟩,hs⟩
  dsimp only at hl
  subst k
  have hc : χr=χs := congrArg (fun q=>q.val.2.1) h
  have hp : ψr=ψs := congrArg (fun q=>q.val.2.2.1) h
  have hz : zr=zs := Subtype.ext (congrArg (fun q=>q.val.2.2.2.val) h)
  subst χs ψs zs
  rfl

@[simp] theorem main_low_original_label_row_cost {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→ Original) (d : Original→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d (embed l)).block))
    (second : Bool) (t : ℝ) (Ds : Finset (Ideal O)) :
    highNormalizedRowCost second d (mainLowOriginalLabelRow embed d r) t Ds=
      highNormalizedRowCost second (fun l=>d (embed l)) r t Ds := rfl

/-- The complete low ordinary image embeds into the full original second
family before its coarse theorem, without a row or label fee. -/
theorem actual_main_low_physical_full_original_row_cost {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→ Original) (hinj : Function.Injective embed)
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Original→ SecondInputDatum α)
    (χ₀ : Label→ RayFourExpansion.RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (coefficient : Original→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
        (fun _=>True)→ BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second
      (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
      (fun l=>coefficient (embed l)) t u select=
      ∑r∈((mainLowPhysicalOrdinaryRows second
        (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l)) select).image
          (ordinaryHighOriginalRow (fun l=>d (embed l)) χ₀ Q m hrows)).image
            (mainLowOriginalLabelRow embed d),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_original_row_cost N a ap second
    (fun l=>d (embed l)) χ₀ Q m hrows (fun l=>coefficient (embed l)) t u select]
  rw [Finset.sum_image (fun r _ z _ heq=>
    main_low_original_label_row_injective embed hinj d heq)]
  apply Finset.sum_congr rfl
  intro r _
  rfl

set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowPhysicalBinSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
        (hT : 2< Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
        (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle61.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
          (Tfirst : ℝ)(hTfirst : 1≤ Tfirst)(hp : p≤ Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(χ ψ : RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
          (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        ∃select : (r : rows)→ ordinaryRows r→ BufferIndex e,
          (∀r,select r=canonical r) ∧
          (∀r pbin z,z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin→ 1≤ pbin.1.val) ∧
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowFixedRayPhysicalCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ select≤
          (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
            ((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))

attribute [local irreducible] MainLowPhysicalBinSpec actual_main_low_quantitative_bins
  MainLowQuantitativeBinSpec geometryMainNonzeroBlocks
set_option maxHeartbeats 320000 in
def actual_main_low_physical_bins {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L) (hτgap : 2*τ< d*η) (hBmassNorm : Bmass≤ Bnorm) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0< Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          MainLowPhysicalBinSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let k:=actual_main_low_quantitative_bins (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0 hτgap hBmassNorm
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2] with Z hz
  refine ⟨hz.1,?_⟩
  unfold MainLowPhysicalBinSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray ordinaryRows canonical
  have hzq:=hz.2
  unfold MainLowQuantitativeBinSpec at hzq
  obtain ⟨select,heq,hpos,hbins,hfull⟩:=hzq hZ s θ w σ freq heightV height mesh hcard hmass
    hsupply' hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff reflected second R seed₀ bin t firstIndex
    hf₁ hw₁ hw₂ hsource Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox B₂ rwitness hf₂ χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale
  refine ⟨select,heq,hpos,?_⟩
  intro src Ds unionDs firstMass physical error exponentFull factor coefficient value t₀ u hshift hseed
  have hb:=fixed_ray_source_transport (Label:=rows) N supply ap second
    (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
    (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ select coefficient value _
    (lowerFactor_pos N supply ap hsupply hap)
    (fun _ _=>rfl)
    (fun r D z=>by
      change ‖normalizedColumn
        (withHeight (datum r).input (if second then (datum r).τ ψ⁻¹ else (datum r).τ χ)
          (t+2*Real.pi*(u-(if second then -t₀ else t₀))))
        (if second then (datum r).D else (datum r).C) _ (datum r).R (datum r).seed D z‖^2=_
      rw [←hshift,←hseed r]
      cases second <;> rfl)
    hfull
  convert hb using 1
  ring

/-- The kernel's actual signed height is paid by the same envelope used
by the all-height splice; neither Mellin variable is dropped. -/
theorem main_low_physical_signed_height (second : Bool) (v height t u : ℝ)
    (hh : 0≤ height) :
    1+|v+2*Real.pi*(u-(if second then -t else t))|+height≤
      2*(1+|v|+height+2*Real.pi*(|t|+|u|)) := by
  have hs : |(if second then -t else t)|=|t| := by cases second <;> simp
  have hsub : |u-(if second then -t else t)|≤|u|+|t| := by
    simpa only [sub_zero,zero_sub,abs_neg,hs] using
      abs_sub_le u 0 (if second then -t else t)
  have hshift : |v+2*Real.pi*(u-(if second then -t else t))|≤
      |v|+2*Real.pi*(|u|+|t|) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hsub
      (show 0≤2*Real.pi by positivity)) |v|
  have hp : 0≤2*Real.pi*(|t|+|u|) := by positivity
  linarith [abs_nonneg v]

/-- Collapse the genuine kernel's exact sixteen, finite buffered-bin fee,
fixed rays and BOTH common-projector/absolute-box fees into the small-height
form. The original reciprocal seed and physical outer factor are retained. -/
theorem main_low_physical_small_fee_bound
    (N degree : ℕ) (e : ℝ) (second : Bool)
    (a ap Cg Cu Cfirst Cbox b Cs control v height t u physical Z exponent seedNorm
      εfirst εsecond εbox : ℝ) (boxCard : ℕ)
    (hlower : 0< lowerFactor N a ap)
    (hCg : 0≤ Cg)(hCu : 0≤ Cu)(hfirst : 0≤ Cfirst)
    (hCs : 0≤ Cs)(hh : 0≤ height)(hphysical : 0≤ physical)(hZ : 0< Z)(hseed : 0< seedNorm)
    (hbox : (boxCard:ℝ)≤ Cbox*Z^εbox) :
    (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Cfirst*Z^εfirst*
      ((1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*mainLowQuantitativeFactor Cg b Cs control
          (v+2*Real.pi*(u-(if second then -t else t))) height physical Z exponent seedNorm
          N degree boxCard)*(Cu*Z^εsecond))))≤
      ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
        (1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*16*Cg*
        (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox)*
        control^2*physical*Z^(exponent+εfirst+εsecond+εbox)/seedNorm*
        (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^degree := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hheight:=pow_le_pow_left₀ (by positivity :
      0≤1+|v+2*Real.pi*(u-(if second then -t else t))|+height)
    (main_low_physical_signed_height second v height t u hh) degree
  unfold mainLowQuantitativeFactor
  calc
    _≤(Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Cfirst*Z^εfirst*
      ((1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*(Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
          (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^degree*(Cbox*Z^εbox)*physical*
          Z^exponent/seedNorm))*(Cu*Z^εsecond)))) := by
      gcongr
    _=_ := by rw [Real.rpow_add hZ,Real.rpow_add hZ,Real.rpow_add hZ]; ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_source_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_complete_physical_reindex

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_fixed_ray_physical_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_fixed_ray_sum_le

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_bins

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_fixed_ray_sigma
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_first_shell_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_complete_ray_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_first_shell_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_ordinary_row_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_original_row_cost

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_original_label_row_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_original_label_row_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_full_original_row_cost

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_main_low_physical_first_shell_contraction

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_signed_height
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_small_fee_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowPhysicalPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowFinalPayment; sha256 4024f9be7736a3fd96aed65df821387263b9bec84b1921fb7ae843adab4cf311 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                  
                                                                 
                                                           

set_option autoImplicit false
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentSourceRow LocalMoment CenteredMomentFirstDiscardedEnergy
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainLowFinalSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

set_option maxHeartbeats 10000 in
private theorem filtered_first_shell_sum {ι J : Type*} [Fintype J]
    {src : ι→ FirstBlockSource}(column : J→ FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : J→ Type*)[∀l,Fintype (Block l)]
    (rows : Finset ((l : J)×Block l))(f : ((l : J)×Block l)→ℝ) :
    (∑q∈rows,f q)=∑n∈selectedShells (selectedFirstProjectors column),
      ∑q∈(Finset.univ.filter (fun q : (l : SelectedFirstShell column n)×Block l.val=>
        (⟨q.1.val,q.2⟩ : (l : J)×Block l)∈rows)),f ⟨q.1.val,q.2⟩ := by
  have heq : rows=Finset.univ.filter (fun q=>q∈rows) := by ext; simp
  calc
    _=∑l,∑q : Block l,if (⟨l,q⟩ : (l : J)×Block l)∈rows then f ⟨l,q⟩ else 0 := by
      nth_rw 1 [heq]
      rw [Finset.sum_filter,Fintype.sum_sigma]
    _=∑n∈selectedShells (selectedFirstProjectors column),
      ∑l : SelectedFirstShell column n,∑q : Block l.val,
        if (⟨l.val,q⟩ : (l : J)×Block l)∈rows then f ⟨l.val,q⟩ else 0 :=
      selected_first_shell_sum column hs _
    _=_ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_filter,Fintype.sum_sigma]

private theorem filtered_first_shell_subtype_sum {ι J : Type*} [Fintype J]
    {src : ι→ FirstBlockSource}(column : J→ FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : J→ Type*)[∀l,Fintype (Block l)]
    (rows : Finset ((l : J)×Block l))(cost : rows→ℝ) :
    (∑q : rows,cost q)=∑n∈selectedShells (selectedFirstProjectors column),
      ∑q : (Finset.univ.filter (fun q : (l : SelectedFirstShell column n)×Block l.val=>
        (⟨q.1.val,q.2⟩ : (l : J)×Block l)∈rows)),
        cost ⟨⟨q.val.1.val,q.val.2⟩,(Finset.mem_filter.mp q.property).2⟩ := by
  let f : ((l : J)×Block l)→ℝ := fun q=>if h : q∈rows then cost ⟨q,h⟩ else 0
  have hg := filtered_first_shell_sum column hs Block rows f
  have hl : (∑q∈rows,f q)=∑q : rows,cost q := by
    rw [←Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro q _
    simp only [f,dite_eq_left q.property]
  rw [hl] at hg
  rw [hg]
  apply Finset.sum_congr rfl
  intro n _
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro q _
  simp only [f,dite_eq_left (Finset.mem_filter.mp q.property).2]

variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
variable (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

/-- A named type boundary keeps the actual second-source family intact. -/
def MainLowFinalSecondIndex (l : Label) : Type :=
  GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key (firstIndex l)

local instance mainLowFinalBlockFintype (l : Label) :
    Fintype (MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l) :=
  inferInstanceAs (Fintype (GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    (firstIndex l)))

/-- Pull the actual complete second index back to one shell of the common
FIRST projector union. The second allocation and all four dyads are kept. -/
def mainLowShellIndex (n : ℤ)
    (q : (l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n)×
      MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l.val) :
    (l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l := ⟨q.1.val,q.2⟩

omit [DecidableEq α] in
theorem main_low_shell_index_injective (n : ℤ) :
    Function.Injective (mainLowShellIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      firstIndex n) := by
  intro q r h
  have hl : q.1=r.1 := Subtype.ext (congrArg Sigma.fst h)
  exact Sigma.ext hl (Sigma.mk.inj_iff.mp h).2

/-- ORIGINAL full-nonzero membership is tested before ordinary restriction
and is pulled back exactly, rather than replaced by restricted nonzeroness. -/
def mainLowShellRows
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)) (n : ℤ) :
    Finset ((l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n)×
      MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l.val) :=
  Finset.univ.filter (fun q=>mainLowShellIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    firstIndex n q∈rows)

def mainLowShellRowOriginal
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)) (n : ℤ)
    (q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n) : rows :=
  ⟨mainLowShellIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex n q.val,
    (Finset.mem_filter.mp q.property).2⟩

attribute [local irreducible] geometryMainNonzeroBlocks geometryLowSecondDatum

set_option maxHeartbeats 320000 in
theorem main_low_shell_original_gate
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l))
    (hOriginal : ∀q∈rows,
      (⟨firstIndex q.1,q.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
        N hZ key)∈geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (n : ℤ) :
    ∀q∈mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n,
      (⟨firstIndex q.1.val,q.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
        N hZ key)∈geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ := by
  intro q hq
  exact hOriginal _ (Finset.mem_filter.mp hq).2

/-- The original selected datum is unchanged under the shell pullback. -/
theorem main_low_shell_datum
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)) (n : ℤ)
    (q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n) :
    geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (firstIndex q.val.1.val) hz₁ hz₂ q.val.2=
    geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (firstIndex (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        firstIndex rows n q).val.1) hz₁ hz₂
      (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        firstIndex rows n q).val.2 := rfl

attribute [local irreducible] MainLowFinalSecondIndex

set_option maxHeartbeats 10000 in
omit [DecidableEq α] in
/-- The entire original-nonzero second-block cost is disintegrated by
one common first-projector shell. No second label, allocation or dyad is
removed, duplicated or charged by its cardinality. -/
theorem main_low_shell_complete_sum
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l))
    (hs : ∀l,Squarefree (firstIndex l).1.val.2.1.val)
    (cost : ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)→ℝ) :
    (∑q∈rows,cost q)=∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
      ∑q∈mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n,
        cost (mainLowShellIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          firstIndex n q) := by
  exact filtered_first_shell_sum (fun l=>(firstIndex l).1.val) hs
    (fun l=>MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l) rows cost

omit [DecidableEq α] in
/-- The same complete filter identity for the original cost's subtype. -/
theorem main_low_shell_complete_subtype_sum
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key firstIndex l))
    (hs : ∀l,Squarefree (firstIndex l).1.val.2.1.val)(cost : rows→ℝ) :
    (∑q : rows,cost q)=∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
      ∑q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n,
        cost (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          firstIndex rows n q) := by
  exact filtered_first_shell_subtype_sum (fun l=>(firstIndex l).1.val) hs
    (fun l=>MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)
    rows cost

/-- The literal complete fixed-ray physical cost follows the same first
shell disintegration, with every residual divisor and signed source row. -/
theorem main_low_shell_fixed_ray_cost
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key firstIndex l))
    (hs : ∀l,Squarefree (firstIndex l).1.val.2.1.val)
    (Ncost : ℕ)(lo ap : ℝ)(second : Bool)(d : rows→ SecondInputDatum α)
    (coefficient : rows→ℝ)(t₀ u : ℝ)(χ ψ : RayFourExpansion.RayCharacter){e : ℝ}
    (select : (r : rows)→ mainLowSourceRows second (d r) (fun _=>True)→ BufferIndex e) :
    mainLowFixedRayPhysicalCost Ncost lo ap second d coefficient t₀ u χ ψ select=
      ∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
        mainLowFixedRayPhysicalCost Ncost lo ap second
          (fun q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n=>
            d (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n q))
          (fun q=>coefficient (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n q))
          t₀ u χ ψ
          (fun q=>select (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n q)) := by
  unfold mainLowFixedRayPhysicalCost
  exact main_low_shell_complete_subtype_sum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    firstIndex rows hs _

include hz₁ hz₂ in
/-- Actual original caps bound the radical bin endpoint on every occupied
common first shell. The selected allocation and its injection are retained. -/
theorem actual_main_low_final_shell_first_gates
    (Bmass Bnorm : ℝ)(hZ2 : 2≤ Z)(hs : Squarefree seed)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
    (hBnorm : Bmass+1≤ Bnorm)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val)))
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      R s.ν s.W s.P≠0)
    (n : ℤ)(hn : n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))) :
    Function.Injective (fun l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n=>
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l.val).1.val,
        (firstIndex l.val).1.val.2.1.val)) ∧
    (∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      frozenCoefficient (firstIndex l.val).2.val
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l.val).1.val)
        R s.ν s.W s.P≠0) ∧
    (∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      dyadicScale n≤((firstIndex l.val).1.val.2.1.val.absNorm:ℝ) ∧
        ((firstIndex l.val).1.val.2.1.val.absNorm:ℝ)<2*dyadicScale n) ∧
    ((key.2 2:ℝ)+1)*Real.logb Z 2≤ Bnorm := by
  have hg:=actual_main_low_first_shell_restriction reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstIndex hinj hf n
  have hp:=actual_main_low_first_shell_scalar_gates reflected s R seed (Z^Mrow) Z ξ Bmass
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hZ2 hs hz₁ hz₂ hsource key firstIndex n hn
  exact ⟨hg.1,hg.2.1,hg.2.2,hp.1.trans hBnorm⟩

attribute [local semireducible] MainLowFinalSecondIndex

/-- Literal full-nonzero physical labels, pulled back before the row sum. -/
def mainLowShellOriginalBlock
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key firstIndex l))
    (hOriginal : ∀q∈rows,
      (⟨firstIndex q.1,q.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
        N hZ key)∈geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (n : ℤ)
    (q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n) :
    geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ :=
  ⟨⟨firstIndex q.val.1.val,q.val.2⟩,
    hOriginal _ (Finset.mem_filter.mp q.property).2⟩

set_option maxHeartbeats 320000 in
/-- A single second common allocation and genuine original row witness
are chosen before the entire signed ordinary source sum on the shell. -/
theorem actual_main_low_final_shell_choices
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key firstIndex l))
    (hOriginal : ∀q∈rows,
      (⟨firstIndex q.1,q.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
        N hZ key)∈geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (n : ℤ)(second : Bool) :
    let d:=fun q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n=>
      geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        (firstIndex q.val.1.val) hz₁ hz₂ q.val.2
    ∃B₂ : (q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n)→
        actualAllocations (d q).input.pools (if second then (d q).D else (d q).C),
      ∃_rwitness : (q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n)→
          secondLiveRows (fun _:Unit=>(d q).block),
        ∀q,frozenCoefficient (B₂ q).val (if second then (d q).D else (d q).C) (d q).R
          (d q).input.ν (d q).input.W (d q).input.P≠0 ∧
          (d q).inactive∈inactiveSubsets (d q).C (d q).D := by
  exact actual_main_low_family_choices reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
    (mainLowShellOriginalBlock reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
      firstIndex rows hOriginal n) second

/-- A pure physical block cost boundary; it keeps the full signed source sum. -/
def mainLowSingleRayPhysicalCost (N : ℕ)(lo ap : ℝ)(second : Bool)
    (datum : SecondInputDatum α)(coefficient t₀ u : ℝ)(χ ψ : RayFourExpansion.RayCharacter){e : ℝ}
    (select : mainLowSourceRows second datum (fun _=>True)→ BufferIndex e) : ℝ :=
  mainLowFixedRayPhysicalCost N lo ap second (fun _:Unit=>datum) (fun _=>coefficient) t₀ u χ ψ
    (fun _=>select)

/-- Grouping costs uses entire source columns before any shell or scalar payment. -/
theorem main_low_single_ray_physical_sum {J : Type*}[Fintype J]
    (N : ℕ)(lo ap : ℝ)(second : Bool)(datum : J→ SecondInputDatum α)
    (coefficient : J→ℝ)(t₀ u : ℝ)(χ ψ : RayFourExpansion.RayCharacter){e : ℝ}
    (select : (r : J)→ mainLowSourceRows second (datum r) (fun _=>True)→ BufferIndex e) :
    mainLowFixedRayPhysicalCost N lo ap second datum coefficient t₀ u χ ψ select=
      ∑r,mainLowSingleRayPhysicalCost N lo ap second (datum r) (coefficient r) t₀ u χ ψ (select r) := by
  unfold mainLowFixedRayPhysicalCost mainLowSingleRayPhysicalCost
  apply Finset.sum_congr rfl
  intro r _
  simp only [mainLowFixedRayPhysicalCost,Fintype.sum_unique]
  rfl

section SavedKernel
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤ H)
open Set HeckePrimeAnnular Cycle61Moment CenteredMomentSlotRatios
/-- A structural common-projector count, uniform over the original slot type. -/
def MainLowFirstShellCountAt (N : ℕ) (U εfirst Cfirst Z : ℝ) : Prop :=
  ∀{ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
    (s : Input ι),Fintype.card ι≤ N →
    (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
    ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)),
    ((selectedShells (selectedFirstProjectors column)).card:ℝ)≤ Cfirst*Z^εfirst

set_option maxHeartbeats 100000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowFinalPhysicalSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (εfirst Cfirst : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
        (hT : 2< Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
        (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle61.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin firstIndex l))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(χ ψ : RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
          (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowFixedRayPhysicalCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ canonical≤
          (Cfirst*Z^εfirst)*((1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
            ((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))))

private theorem main_low_quantitative_factor_nonneg
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ) (hCg : 0≤ Cg) (hCs : 0≤ Cs)
    (hh : 0≤ height) (hp : 0≤ physical) (hZ : 0≤ Z) (hs : 0≤ seedNorm) :
    0≤ mainLowQuantitativeFactor Cg b Cs control v height physical Z exponent seedNorm N degree boxCard := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  unfold mainLowQuantitativeFactor
  positivity

attribute [local irreducible] mainLowFixedRayPhysicalCost mainLowCanonicalSelector

set_option maxHeartbeats 60000 in
theorem main_low_final_physical_spec_of_bins {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (εfirst Cfirst : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (Z : ℝ)(hZ2 : 2≤ Z)(hCg : 0< Cg)(hCu : 0< Cu)(hBstrong : Bmass+1≤ Bnorm)
    (hcount : MainLowFirstShellCountAt N U εfirst Cfirst Z)
    (hspec : MainLowPhysicalBinSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z) :
    MainLowFinalPhysicalSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst degree Sp Cg Cu η₀ Q hQM hQ72 Z := by
  unfold MainLowFinalPhysicalSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hinj
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray ordinaryRows canonical src Ds unionDs firstMass physical error exponentFull
    factor coefficient value t₀ u hshift hseed
  let column:=fun l=>(firstIndex l).1.val
  have hshellCount := hcount (ι:=α) (Label:=Label) s hcard hpool R seed₀ (Z^Mrow) ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin column
  have hsq : ∀l,Squarefree (column l).2.1.val :=
    fun l=>actual_first_live_squarefree _ _ _ (firstIndex l).1.property
  let E:=(1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
    ((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))
  have hphysical : 0≤ physical := (geometry_high_factor_pos reflected
    (geometrySupportConstant N supply ap ap) bin
    (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  have hfactor : 0≤ factor := main_low_quantitative_factor_nonneg Cg b Cs (p₀.control Sp)
    heightV height physical Z exponentFull (seed₀.absNorm:ℝ) N degree box.card
    hCg.le (le_trans zero_le_one hCs) hheight hphysical (zero_lt_one.trans hZ).le (Nat.cast_nonneg _)
  have hE : 0≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one
      (lowerFactor_pos N supply ap hsupply hap).le) (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hfactor)
        (mul_nonneg hCu.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
  rw [main_low_shell_fixed_ray_cost reflected s R seed₀ Z Mrow amp ξ reserve bs t
    (Fintype.card α) hZ bin firstIndex rows hsq N]
  calc
    _≤∑_n∈selectedShells (selectedFirstProjectors column),E := by
      apply Finset.sum_le_sum
      intro n hn
      let rs:=mainLowShellRows reflected s R seed₀ Z Mrow amp ξ reserve bs t (Fintype.card α) hZ bin firstIndex rows n
      let old:=mainLowShellRowOriginal reflected s R seed₀ Z Mrow amp ξ reserve bs t (Fintype.card α) hZ bin firstIndex rows n
      let fi:=fun l : SelectedFirstShell column n=>firstIndex l.val
      have hg:=actual_main_low_final_shell_first_gates reflected s R seed₀ Z Mrow ξ hZ bin hw₁ hw₂
        firstIndex Bmass Bnorm hZ2 hs₀ hsourceOriginal hBstrong hinj hf₁ n hn
      have hTfirst:=(actual_geometry_selected_first_shell_scale s N R seed₀ (Z^Mrow) Z ξ U
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hcard hZ.le hUcap hpool bin column n hn).1
      have hk:=hspec
      unfold MainLowPhysicalBinSpec at hk
      have hkfirst:=hk hZ s θ w σ freq heightV height mesh hcard hmass
        hsupply' hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
        Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff reflected second R seed₀ bin t fi
        hg.2.1 hw₁ hw₂ (fun l=>hsource l.val) (dyadicScale n) hTfirst hg.2.2.2 hs₀ hs₀0 hg.1 hg.2.2.1

      have hkrows:=hkfirst rs
      have hko:=hkrows (main_low_shell_original_gate reflected s R seed₀ Z Mrow amp ξ reserve bs t (Fintype.card α)
          hZ bin hw₁ hw₂ firstIndex rows hOriginal n)
      have hku:=hko (fun r hr=>hU (old ⟨r,hr⟩).val (old ⟨r,hr⟩).property)
      have hkbox:=hku box
        (fun r hr=>hbox (old ⟨r,hr⟩).val (old ⟨r,hr⟩).property)

      have hkb:=hkbox (fun r=>B₂ (old r))
      have hkw:=hkb (fun r=>rwitness (old r))
      have hkf:=hkw (fun r=>hf₂ (old r))
      have hkchar:=hkf (fun r=>χ₀ (old r)) χ ψ m hm₀ hml hm₂
      have hkp:=hkchar (fun r=>hP (old r)) (fun r=>hPN (old r))
      have hkd:=hkp (fun r=>divisorSeed (old r)) (fun r=>hE₂ (old r)) (fun r=>hdivisor (old r))
      have hkp0:=hkd p₀ hp₁ hp₂ Ψ
      have hks:=hkp0 hsourceOriginal hplain₁ hplain₂ hpool hwindowSource hplainScale
      obtain ⟨select,heq,_hpos,hcost⟩:=hks
      have hsel := funext heq
      have hb:=hcost t₀ u hshift (fun r=>hseed (old r))
      subst select
      exact hb
    _=((selectedShells (selectedFirstProjectors column)).card:ℝ)*E:=by simp
    _≤(Cfirst*Z^εfirst)*E:=mul_le_mul_of_nonneg_right hshellCount hE

attribute [local irreducible] MainLowFinalPhysicalSpec MainLowPhysicalBinSpec
set_option maxHeartbeats 100000 in
def actual_main_low_final_physical_bins {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L) (hτgap : 2*τ< d*η) (hBstrong : Bmass+1≤ Bnorm) (εfirst : ℝ)(hefirst : 0<εfirst) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,ΣCfirst : ℝ,
      PLift (0< Cu ∧ 0< Cfirst) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          MainLowFinalPhysicalSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let counts:=eventual_actual_geometry_selected_first_shell_subpower N U εfirst hUcap hefirst
  let Cfirst:=Classical.choose counts
  have hCfirst:= (Classical.choose_spec counts).1
  have hcount:= (Classical.choose_spec counts).2
  let k:=actual_main_low_physical_bins (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0 hτgap (by linarith)
  refine ⟨k.1,k.2.1,k.2.2.1,Cfirst,PLift.up ⟨k.2.2.2.1.down,hCfirst⟩,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2,hcount] with Z hz hf
  refine ⟨hz.1,?_⟩
  have hcountZ : MainLowFirstShellCountAt N U εfirst Cfirst Z := hf.2
  exact main_low_final_physical_spec_of_bins (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst k.1 k.2.1 hc.1 k.2.2.1 η₀ Q hQM hQ72 Z hz.1 hc.2.down.1 k.2.2.2.1.down hBstrong hcountZ hz.2

end SavedKernel

#print axioms filtered_first_shell_sum

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_shell_index_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_shell_original_gate
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_shell_datum


#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_shell_complete_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_shell_complete_subtype_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_shell_fixed_ray_cost

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_final_shell_first_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_final_shell_choices

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_final_physical_spec_of_bins

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_single_ray_physical_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_final_physical_bins

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowFinalPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowCompletePayment; sha256 91939814facd366188096f978704fb5605b199ab796425ccd68df756155e8682 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                               
                                                                    
                                                                       
                                                       
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowCompleteDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable


/- The complete canonical ordinary low family, with both fixed ray sums,
exact buffer/sixteen fees and the absolute-box subpower payment composed.
The original full-nonzero filter and actual reduced second seeds remain literal. -/
set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowCompletePhysicalSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (εfirst Cfirst εbox Cbox : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
        (hT : 2< Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
        (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle61.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hboxCard : (box.card:ℝ)≤ Cbox*Z^εbox)
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
          (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L),
        let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
          mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
            (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
            (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowPhysicalCompleteCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
            (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*16*Cg*
            (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox)*
            (p₀.control Sp)^2*physical*
            Z^(exponentFull+εfirst+(εunion+3*(((N:ℝ)+2)*U)*εshell)+εbox)/(seed₀.absNorm:ℝ)*
            (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree

attribute [local irreducible] mainLowPhysicalCompleteCost mainLowFixedRayPhysicalCost
set_option maxHeartbeats 120000 in
theorem main_low_complete_physical_spec_of_final {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (εfirst Cfirst εbox Cbox : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ)
    (hCg : 0≤ Cg)(hCu : 0≤ Cu)(hfirst : 0≤ Cfirst)
    (hspec : MainLowFinalPhysicalSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst degree Sp Cg Cu η₀ Q hQM hQ72 Z) :
    MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z := by
  unfold MainLowCompletePhysicalSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hinj rows hOriginal hU box hboxCard hbox datum B₂ rwitness hf₂ q g χ₀ m hm₀ hml hm₂
    hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale canonical firstMass physical error exponentFull t₀ u hshift hseed
  have hk:=hspec
  unfold MainLowFinalPhysicalSpec at hk
  have hkfirst:=hk hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff reflected second R seed₀ bin t firstIndex
    hf₁ hw₁ hw₂ hsource hs₀ hs₀0 hinj
  have hkrows:=hkfirst rows hOriginal hU box hbox
  have hkb:=hkrows B₂ rwitness hf₂
  have hray (χ ψ : RayFourExpansion.RayCharacter) :
      mainLowFixedRayPhysicalCost N supply ap second
        (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
        (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ
        (fun r=>canonical r χ ψ)≤
      Cfirst*Z^εfirst*((1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card)*
          (Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))) := by
    exact hkb χ₀ χ ψ m hm₀ hml hm₂ hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ
      hsourceOriginal hplain₁ hplain₂ hpool hwindowSource hplainScale t₀ u hshift hseed
  have hfull := Finset.sum_le_sum (s:=Finset.univ) (fun χ _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun ψ _=>hray χ ψ))
  rw [main_low_physical_complete_ray_sum]
  apply le_trans hfull
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hshift]
  have hseedNorm : 0<(seed₀.absNorm:ℝ) := by
    apply Nat.cast_pos.mpr
    exact Nat.pos_of_ne_zero (fun h=>hs₀0 (Ideal.absNorm_eq_zero_iff.mp h))
  simpa only [pow_two,mul_assoc] using main_low_physical_small_fee_bound N degree e second supply ap Cg Cu Cfirst Cbox b Cs
    (p₀.control Sp) t height t₀ u physical Z exponentFull (seed₀.absNorm:ℝ)
    εfirst (εunion+3*(((N:ℝ)+2)*U)*εshell) εbox box.card
    (lowerFactor_pos N supply ap hsupply hap) hCg hCu hfirst (zero_le_one.trans hCs) hheight
    (geometry_high_factor_pos reflected (geometrySupportConstant N supply ap ap) bin
      (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
    (zero_lt_one.trans hZ) hseedNorm hboxCard

attribute [local irreducible] MainLowCompletePhysicalSpec MainLowFinalPhysicalSpec
set_option maxHeartbeats 100000 in
def actual_main_low_complete_physical_bins {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L) (hτgap : 2*τ< d*η) (hBstrong : Bmass+1≤ Bnorm) (εfirst : ℝ)(hefirst : 0<εfirst) (εbox Cbox : ℝ) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,ΣCfirst : ℝ,
      PLift (0< Cu ∧ 0< Cfirst) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let k:=actual_main_low_final_physical_bins (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      hτgap hBstrong εfirst hefirst
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2] with Z hz
  refine ⟨hz.1,?_⟩
  exact main_low_complete_physical_spec_of_final (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst k.2.2.2.1 εbox Cbox k.1 k.2.1 hc.1 k.2.2.1 η₀ Q hQM hQ72 Z
      hc.2.down.1.le k.2.2.2.2.1.down.1.le k.2.2.2.2.1.down.2.le hz.2

open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonPairedSource

/-- Exact ordinary image of the selected original blocks, retaining both rays and the signed row. -/
def mainLowCompleteImageRows {Label Original : Type*} [Fintype Label] [Fintype Original]
    (embed : Label→ Original)(d : Original→ SecondInputDatum α)
    (χ₀ : Label→ RayFourExpansion.RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (second : Bool){e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
        (fun _=>True)→ BufferIndex e) :=
  ((mainLowPhysicalOrdinaryRows second
    (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l)) select).image
      (ordinaryHighOriginalRow (fun l=>d (embed l)) χ₀ Q m hrows)).image
        (mainLowOriginalLabelRow embed d)

theorem main_low_complete_image_cost {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→ Original)(hinj : Function.Injective embed)
    (N : ℕ)(a ap : ℝ)(second : Bool)(d : Original→ SecondInputDatum α)
    (χ₀ : Label→ RayFourExpansion.RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (coefficient : Original→ℝ)(t u : ℝ){e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
        (fun _=>True)→ BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second
      (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
      (fun l=>coefficient (embed l)) t u select=
    ∑r : mainLowCompleteImageRows embed d χ₀ Q m hrows second select,
      (coefficient r.val.val.1*((d r.val.val.1).K/lowerFactor N a ap)*
        normalizer (d r.val.val.1).C (d r.val.val.1).D (d r.val.val.1).inactive)*
      highNormalizedRowCost second d r.val
        ((d r.val.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_full_original_row_cost embed hinj]
  exact (Finset.sum_coe_sort _ _).symm

private theorem low_complete_scalar_sum {J : Type*}[Fintype J]
    (mass radius volume normal value : J→ℝ)(lower : ℝ) :
    (∑r,mass r/volume r*(radius r/lower)*normal r*value r)=
      ∑r,mass r*(radius r/volume r)*normal r/lower*value r := by
  apply Finset.sum_congr rfl
  intro r _
  ring

attribute [local irreducible] mainLowCompleteImageRows

def MainLowCompleteCoarseSpec {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U exponent K Z : ℝ) : Prop :=
    ∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |Dfirst|≤ B →
      |a|≤ B → |frequencyLoss Z 32 ξ+reserve|≤ B → (∀j,s.M j≤ Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤ window) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^plainCap) →
      (∀j,s.P j≤ Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
      (∀x,s.W₁ x≠0→ ap≤ x) → (∀x,s.W₂ x≠0→ ap≤ x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum : Index→ SecondInputDatum α := fun q=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset Index)(second : Bool)(W : 𝓢(ℝ,ℂ))
        (χ₀ : rows→ RayFourExpansion.RayCharacter)(Q : rows→ Ideal O)(m : rows→ O)
        (t₀ u e control B₁ B₂ : ℝ),
      0≤ control → 0≤ B₁ → 0≤ B₂ →
      (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) → (B₁*B₂)^2≤ control →
      ∀select : (r : rows)→(χ ψ : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (ordinarySecondDatum (datum r.val) (χ₀ r) (Q r) (m r))
          (fun _=>True)→ BufferIndex e,
      mainLowPhysicalCompleteCost N lo ap second
        (fun r : rows=>ordinarySecondDatum (datum r.val) (χ₀ r) (Q r) (m r))
        (fun r=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
          (firstIndex r.val.1).1.val /
          volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
            (firstIndex r.val.1))) t₀ u select≤
        K*control*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^exponent

attribute [local irreducible] MainLowCompleteCoarseSpec
set_option maxHeartbeats 120000 in
theorem main_low_complete_coarse_spec_of_original {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U exponent K Z : ℝ)
    (hc : MainHighCoarseSideSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U exponent K Z) :
    MainLowCompleteCoarseSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U exponent K Z := by
  unfold MainLowCompleteCoarseSpec
  intro hZ Label _ reflected s R seed Dfirst a reserve t hK hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    rows second W χ₀ Q m t₀ u e control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB select
  have hk:=hc
  unfold MainHighCoarseSideSpec at hk
  have hkfirst:=hk hZ reflected s R seed Dfirst a reserve t hK hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc
  let coefficient : Index→ℝ:=fun r=>
    geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin (firstIndex r.1).1.val /
      volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t (firstIndex r.1))
  have hrows : ∀r : rows,(datum r.val).rows=sourceRows
      (datum r.val).C (datum r.val).D (datum r.val).inactive (datum r.val).radius := by
    intro r
    rfl
  let imageRows:=mainLowCompleteImageRows (fun r : rows=>r.val) datum χ₀ Q m hrows second select
  rw [main_low_complete_image_cost (fun r : rows=>r.val) Subtype.val_injective
    N lo ap second datum χ₀ Q m hrows coefficient t₀ u select]
  have hraw:=hkfirst imageRows second W
    (fun r=>(datum r.val.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
    (fun r=>(datum r.val.val.1).block.divisors.filter Squarefree)
    control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB
    (fun r D hD=>Finset.mem_filter.mp hD)
  have hdatumK : ∀r : imageRows,(datum r.val.val.1).K=
      firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex r.val.val.1.1).1.val) := fun _=>rfl
  simp_rw [←hdatumK] at hraw
  change (∑r : imageRows,
    (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
      (firstIndex r.val.val.1.1).1.val /
      volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
        (firstIndex r.val.val.1.1)))*((datum r.val.val.1).K/lowerFactor N lo ap)*
      normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive*
      highNormalizedRowCost second datum r.val
        ((datum r.val.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.val.1).block.divisors.filter Squarefree))≤ _
  rw [low_complete_scalar_sum]
  exact hraw

/-- This degree depends only on the scalar coarse exponent, target floor,
common positive tau and already saved low degree. -/
def mainLowCompleteHeightDegree (coarse targetMin τ : ℝ)(hτ : 0<τ)(smallDegree : ℕ) : ℕ :=
  Classical.choose (geometry_uniform_shifted_height_splice coarse targetMin τ hτ smallDegree)

def mainLowCompleteFee (N : ℕ)(e supply ap Cg Cu Cfirst Cbox b Cs : ℝ) : ℝ :=
  (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
    (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*16*Cg*
    (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox

def mainLowCompleteHeightConstant (N degreeAll : ℕ)(e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse : ℝ) : ℝ :=
  (2+4*Real.pi)^degreeAll*(1+mainLowCompleteFee N e supply ap Cg Cu Cfirst Cbox b Cs+Kcoarse)

open CenteredMomentNaturalRowSource

theorem actual_main_low_complete_coarse_payment {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤ N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hε : 0<ε)(hpad : 0< pad)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)(hwindow : 0≤ window)(hcap : 0≤ plainCap)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤ loss)(hU : 0≤ U) :
    ∃K : ℝ,0< K ∧ ∀ᶠ Z : ℝ in atTop,
      MainLowCompleteCoarseSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U
        (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z := by
  obtain ⟨K,hK,hc⟩:=actual_main_high_original_coarse_side_payment
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  refine ⟨K,hK,?_⟩
  filter_upwards [hc] with Z hz
  exact main_low_complete_coarse_spec_of_original N B Cs b bs window plainCap lo ap εmass ξ U
    (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z hz


set_option linter.unusedVariables false in
set_option linter.defProp false in
set_option maxHeartbeats 180000 in
def MainLowCompleteAllHeightSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin Kall : ℝ)(degreeAll : ℕ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤ N)(hmass : ∀j,s.M j≤ Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤ Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤ hi)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
        (hT : 2< Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤ Mrow)
        (hω : 0≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤ Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle61.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)(hseedOne : seed₀=1)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hboxCard : (box.card:ℝ)≤ Cbox*Z^εbox)
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤ window)
          (hplainScale : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^L)
          (hend : Endpoints b bs bs s)
          (hsourceCoarse : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^Bcoarse)
          (hvolumeCoarse : |Real.logb Z (volume s)|≤ Bcoarse)
          (hMrowCoarse : |Mrow|≤ Bcoarse)(hampCoarse : |amp|≤ Bcoarse)
          (homegaCoarse : |frequencyLoss Z 32 ξ+reserve|≤ Bcoarse)
          (hscalesCoarse : ∀side j,Cycle61.Physical.sourcePlainScales s.toData.toSource side j≤ Z^plainCap)
          (hprimeCoarse : ∀j,s.P j≤ Z^plainCap)
          (hamp0 : 0≤ amp)(hreserve0 : 0≤ reserve)(hξeq : ξ=ξ₀)
          (B₁ B₂ : ℝ)(hB₁ : 0≤ B₁)(hB₂ : 0≤ B₂)
          (hnorm₁ : ∀x,‖s.W₁ x‖≤ B₁)(hnorm₂ : ∀x,‖s.W₂ x‖≤ B₂)
          (hcontrol : (B₁*B₂)^2≤(p₀.control Sp)^2),
        let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
          mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
            (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
            (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let target:=exponentFull+εfirst+(εunion+3*(((N:ℝ)+2)*U)*εshell)+εbox
        ∀(htarget : targetMin≤ target)(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowPhysicalCompleteCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
          Kall*(p₀.control Sp)^2*physical*Z^target*
            (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

attribute [local irreducible] MainLowCompleteAllHeightSpec
set_option maxHeartbeats 140000 in
theorem main_low_complete_all_height_spec_of_receipts {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L)
    (εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin coarse Kcoarse : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M) (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}) (Z : ℝ)
    (hCg : 0≤ Cg)(hCu : 0≤ Cu)(hfirst : 0≤ Cfirst)(hboxC : 0≤ Cbox)(hKcoarse : 0< Kcoarse)
    (hN : N=Fintype.card α)(hbsb : bs=b)
    (hspec : MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z)
    (hc : MainLowCompleteCoarseSpec (α:=α) N Bcoarse Cs b bs window plainCap supply ap
      εmass ξ₀ U coarse Kcoarse Z) :
    0< mainLowCompleteHeightConstant N (mainLowCompleteHeightDegree coarse targetMin τ hτ degree)
      e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse ∧ MainLowCompleteAllHeightSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin
        (mainLowCompleteHeightConstant N (mainLowCompleteHeightDegree coarse targetMin τ hτ degree)
          e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse)
        (mainLowCompleteHeightDegree coarse targetMin τ hτ degree) degree Sp Cg Cu η₀ Q hQM hQ72 Z := by
  subst N bs
  let fee := (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
    (1/lowerFactor (Fintype.card α) supply ap)*(Fintype.card (BufferIndex e):ℝ)*16*Cg*
    (2*b^2*Cs^(4*Fintype.card α))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox
  have hfee : 0≤ fee := by
    dsimp only [fee]
    have hl := (lowerFactor_pos (Fintype.card α) supply ap hsupply hap).le
    have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
    positivity
  let Csmall:=1+fee
  have hCsmall : 0< Csmall := by dsimp only [Csmall]; linarith
  let degreeAll:=mainLowCompleteHeightDegree coarse targetMin τ hτ degree
  have hext:=Classical.choose_spec (geometry_uniform_shifted_height_splice coarse targetMin τ hτ degree)
  let Kall:=(2+4*Real.pi)^degreeAll*(Csmall+Kcoarse)
  have hKall : 0< Kall := by dsimp only [Kall]; positivity
  refine ⟨hKall,?_⟩
  unfold MainLowCompleteAllHeightSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hseedOne hinj rows hOriginal hU box hboxCard hbox datum B₂ rwitness hf₂ q g χ₀ m hm₀ hml hm₂
    hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale hend hsourceCoarse hvolumeCoarse hMrowCoarse hampCoarse homegaCoarse
    hscalesCoarse hprimeCoarse hamp0 hreserve0 hξeq B₁ B₂bound hB₁ hB₂ hnorm₁ hnorm₂ hcontrol
    canonical firstMass physical error exponentFull target htarget t₀ u hshift hseed
  let E:=mainLowPhysicalCompleteCost (Fintype.card α) supply ap second
    (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
    (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical
  have hphysical : 0≤ physical := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card α) supply ap ap) bin
    (geometrySupportConstant_pos (Fintype.card α) supply ap ap hsupply hap hap)).le
  have hsmall : 2*(1+|t|+height+2*Real.pi*(|t₀|+|u|))≤ Z^τ →
      E≤ Csmall*((p₀.control Sp)^2*physical)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree := by
    intro hH
    have hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ := by
      rw [hshift]
      exact main_low_payment_shifted_height_envelope second t height t₀ u (Z^τ)
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hH
    have hs:=hspec
    unfold MainLowCompletePhysicalSpec at hs
    have hsfirst:=hs hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
      Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff reflected second R seed₀ bin t firstIndex
      hf₁ hw₁ hw₂ hsource hs₀ hs₀0 hinj
    have hsrows:=hsfirst rows hOriginal hU box hboxCard hbox
    have hsalloc:=hsrows B₂ rwitness hf₂ χ₀ m hm₀ hml hm₂ hP hPN divisorSeed hE₂ hdivisor
    have hbound:=hsalloc p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool hwindowSource hplainScale
      t₀ u hshift hseed
    have hnorm : (seed₀.absNorm:ℝ)=1 := by rw [hseedOne]; norm_num
    rw [hnorm,div_one] at hbound
    have hbound' : E≤ fee*((p₀.control Sp)^2*physical)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree := by
      convert hbound using 1; ring
    apply hbound'.trans
    have hf : fee≤ Csmall := by dsimp only [Csmall]; linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf (by positivity))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (by positivity)
  have hb : E≤ Kcoarse*((p₀.control Sp)^2*physical)*Z^coarse := by
    have hcξ:=hc
    rw [←hξeq] at hcξ
    unfold MainLowCompleteCoarseSpec at hcξ
    have hcfirst:=hcξ hZ reflected s R seed₀ Mrow amp reserve t
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hs₀ hend hsupply' hsourceCoarse
      hvolumeCoarse hMrowCoarse hampCoarse homegaCoarse hmass hwindowSource hscalesCoarse hprimeCoarse
      hpool hplain₁ hplain₂ hw₁ hw₂ hamp0 hreserve0 bin firstIndex hinj hf₁
    have hcb:=hcfirst rows second Ψ χ₀ (fun _=>internalQ Q η₀) (fun _=>m) t₀ u e
      ((p₀.control Sp)^2) B₁ B₂bound (sq_nonneg _) hB₁ hB₂ hnorm₁ hnorm₂ hcontrol canonical
    simpa only [E,datum,firstMass,childSrc,physical,mul_assoc] using hcb
  have hout:=hext Z target t height t₀ u E Csmall Kcoarse ((p₀.control Sp)^2*physical)
    hZ.le htarget hheight hCsmall.le hKcoarse.le (by positivity) hsmall hb
  dsimp only [mainLowCompleteHeightConstant,mainLowCompleteFee,mainLowCompleteHeightDegree]
  convert hout using 1
  dsimp only [Csmall,fee]
  ring

set_option maxHeartbeats 160000 in
def actual_main_low_complete_all_height_payment {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤ U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤ window)(hpad : 0< pad)(hL0 : 0≤ L) (hτgap : 2*τ< d*η) (hBstrong : Bmass+1≤ Bnorm) (εfirst : ℝ)(hefirst : 0<εfirst) (εbox Cbox : ℝ)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (ξ₀ Bcoarse plainCap targetMin coarseLoss coarseShell coarsePad coarseVolume : ℝ)
    (hN : N=Fintype.card α)(hbsb : bs=b)(hboxC : 0≤ Cbox)
    (hξ₀ : 0≤ξ₀)(hξloss : ξ₀≤ coarseLoss)(hBc : 0≤ Bcoarse)(hpc : 0≤ plainCap)
    (hcloss : 0< coarseLoss)(hcshell : 0< coarseShell)(hcpad : 0< coarsePad)(hcvolume : 0< coarseVolume) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,ΣCfirst : ℝ,
      PLift (0< Cu ∧ 0< Cfirst) ×
      (let coarse:=Bcoarse+(39*(Bcoarse+coarseLoss)+(Bcoarse+coarseLoss)*εmass+
        (Bcoarse+coarseLoss)*coarseShell+coarseVolume)+8*(Bcoarse+coarseLoss)+3*coarseLoss+
        ((N:ℝ)+2)*plainCap+2*coarsePad+3*(((N:ℝ)+2)*U)*coarseShell+Bcoarse
       let degreeAll:=mainLowCompleteHeightDegree coarse targetMin τ hτ degree
       ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
        ΣCg : ℝ,ΣKall : ℝ,PLift (0< Cg ∧ 0< Kall ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          MainLowCompleteAllHeightSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin Kall degreeAll degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let coarse:=Bcoarse+(39*(Bcoarse+coarseLoss)+(Bcoarse+coarseLoss)*εmass+
        (Bcoarse+coarseLoss)*coarseShell+coarseVolume)+8*(Bcoarse+coarseLoss)+3*coarseLoss+
        ((N:ℝ)+2)*plainCap+2*coarsePad+3*(((N:ℝ)+2)*U)*coarseShell+Bcoarse
  have hα : Fintype.card α≤ N := by rw [hN]
  let cr:=actual_main_low_complete_coarse_payment (α:=α) ηcoarse u₀ F₀ R₀ hu₀
    N hα Bcoarse coarseLoss coarseShell coarsePad Cs b bs window plainCap supply ap
    coarseVolume εmass ξ₀ U hBc hcloss hcshell hcpad hCs hb hbs hwindow hpc hsupply hap
    hcvolume hemass hξ₀ hξloss hUcap
  let Kcoarse:=Classical.choose cr
  have hKcoarse:=(Classical.choose_spec cr).1
  have hcoarse:=(Classical.choose_spec cr).2
  let k:=actual_main_low_complete_physical_bins (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      hτgap hBstrong εfirst hefirst εbox Cbox
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,?_⟩
  dsimp only
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  let degreeAll:=mainLowCompleteHeightDegree coarse targetMin τ hτ k.1
  let Kall:=mainLowCompleteHeightConstant N degreeAll e supply ap hc.1 k.2.2.1 k.2.2.2.1 Cbox b Cs Kcoarse
  have hKall : 0< Kall := by
    dsimp only [Kall,mainLowCompleteHeightConstant,mainLowCompleteFee]
    have hCu:=k.2.2.2.2.1.down.1
    have hfirst:=k.2.2.2.2.1.down.2
    have hCg:=hc.2.down.1
    have hdiag:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
    have hlower:=(lowerFactor_pos N supply ap hsupply hap).le
    have hCs0:=zero_le_one.trans hCs
    positivity
  refine ⟨hc.1,Kall,PLift.up ⟨hc.2.down.1,hKall,?_⟩⟩
  filter_upwards [hc.2.down.2,hcoarse] with Z hz hcz
  refine ⟨hz.1,?_⟩
  exact (main_low_complete_all_height_spec_of_receipts (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst k.2.2.2.1 εbox Cbox ξ₀ Bcoarse plainCap targetMin coarse Kcoarse
      k.1 k.2.1 hc.1 k.2.2.1 η₀ Q hQM hQ72 Z
      hc.2.down.1.le k.2.2.2.2.1.down.1.le k.2.2.2.2.1.down.2.le hboxC hKcoarse
      hN hbsb hz.2 hcz).2

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_complete_physical_spec_of_final

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_complete_physical_bins

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_complete_coarse_spec_of_original

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_complete_image_cost

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_complete_all_height_spec_of_receipts

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_complete_coarse_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_complete_all_height_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowCompletePayment -/
