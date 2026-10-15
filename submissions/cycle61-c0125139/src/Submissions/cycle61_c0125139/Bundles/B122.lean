/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B088
import Submissions.cycle61_c0125139.Bundles.B094
import Submissions.cycle61_c0125139.Bundles.B115
import Submissions.cycle61_c0125139.Bundles.B117
import Submissions.cycle61_c0125139.Bundles.B121
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryNaturalDictionary; sha256 2aa1bacf5df83f5a8da4cd81bf576c9b846dfa2b67ead081ba37e8073e31cd9c -/
section
                                                            

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The actual fixed dictionary unit and first arithmetic label force a
nonzero encoded first frequency. -/
theorem geometry_first_frequency_ne_zero {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j) :
    jointFirstFrequency (!reflected) u₀
      (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0 := by
  apply actual_joint_first_frequency_ne_zero _ _ _ _ hu₀ (Units.ne_zero _)
  change Supported (first r.val.1).1.1
  rw [hfirst]
  exact (geometryFirstSource s R seed K Z ξ hK bin j.1).hC

/-- Both signs of the actual second row have a canonical natural-row
representative in the same fixed two-ray dictionary. All nonzero and Euler
puncture gates follow from the physical input. -/
theorem actual_geometry_natural_dictionary {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((d r.val.1).rows_ne _ r.val.2.2.2.property)
      · exact (d r.val.1).rows_ne _ r.val.2.2.2.property
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let holes := (d r.val.1).input.η.modulus*puncture
    holes≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((d r.val.1).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
        (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro unit hf key₀ key z hz puncture holes
  have hp : puncture≠0 := by
    apply mul_ne_zero hR
    dsimp only [puncture] at *
    split <;> first | exact (d r.val.1).hC.1 | exact (d r.val.1).hD.1
  refine ⟨mul_ne_zero (d r.val.1).input.η.modulus_ne_bot hp,?_⟩
  intro I
  let G := naturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
    (jointFirstFrequency (!reflected) u₀ unit (secondEncodedRow (fun l=>(d l).block) first r)) hf
  cases second
  · exact actual_geometry_second_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      d first r hparent hfirst hf G ψ (naturalRow _ _ hz) hR I
  · exact actual_geometry_second_reflected_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      d first r hparent hfirst hf G ψ (naturalRow _ _ hz) hR I

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_first_frequency_ne_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_natural_dictionary

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryNaturalDictionary -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalNatural.State; sha256 71b5d34abf402136af4c85dda91f9a3564f75b4411215dc11ca8626247534a91 -/
section
                                   
                                             
                                                    
                                                                 

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ActualEisensteinCubic
open CenteredMomentEnergyState CenteredMomentEnergyChildState
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedWidth CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondLiveBlock
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRadicalBudget CenteredMomentFixedRowMask CenteredExceptionalProfile
open Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O

def retainedScale (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) : ℝ :=
  max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
    normValue (nonunitFrequencyGenerator C D U)))

def retainedState (Z Bmask : ℝ) (hZ : 1< Z) (τ : Character) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    NaturalState Z Bmask 2 :=
  daughterState τ Q P ballProfile Z (retainedScale R C D U) Bmask 2
    hZ (le_max_left _ _) hP hPN ball_support ballProfile_nonneg

theorem retainedState_width (Z Bmask : ℝ) (hZ : 1< Z) (τ : Character) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    (retainedState Z Bmask hZ τ Q P hP hPN R C D U).width =
      Real.logb Z (retainedScale R C D U)+Real.logb Z (τ.modulus.absNorm:ℝ) := rfl

theorem retainedState_keep (Z Bmask : ℝ) (hZ : 1< Z) (τ : Character) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) (z : O) :
    (retainedState Z Bmask hZ τ Q P hP hPN R C D U).radial.keep z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  change (z≠0 ∧ ¬FixedInducingRow τ Q (fixedBadMask*idealGenerator P) 1 z) ↔ _
  by_cases hz : z=0
  · simp [hz]
  · rw [fixedInducingRow_mul_mask_iff τ Q fixedBadMask (idealGenerator P) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero P hP) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)]

theorem actual_source_puncture {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α) (C P : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z Bmask Bsource : ℝ) (hZ : 0< Z) (hP : P≠0)
    (hPN : (P.absNorm:ℝ)≤ Z^Bmask) (hCN : (C.absNorm:ℝ)≤ Z^Bsource) :
    P*C≠0 ∧ ((P*C).absNorm:ℝ)≤ Z^(Bmask+Bsource) :=
  ⟨mul_ne_zero hP (CenteredMomentAllocatedNaturalRadial.common_nonzero s C B),
    common_puncture_bound Z Bmask Bsource hZ P C hPN hCN⟩

theorem actual_partRows_majorized (Z Bmask : ℝ) (hZ : 1< Z) (τ : Character)
    (Q P : Ideal O) (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (η : Character) (χ : RayFourExpansion.RayCharacter) (m : O)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) (z : O)
    (hz : z∈CenteredMomentSecondEnergySplit.partRows false η χ Q m C D U R) :
    1≤((retainedState Z Bmask hZ τ Q P hP hPN R C D U).radial.profile
      (normValue z/(retainedState Z Bmask hZ τ Q P hP hPN R C D U).radial.scale)).re := by
  have hs : z∈CenteredMomentSecondEnergySplit.sourceRows C D U R :=
    (Finset.mem_filter.mp hz).1
  have hw := liveRows_weight C D U R _ z hs
  exact Cycle61FinalRadius.actual_retained_majorant R _ _ z hw

section Actual
variable {η : Character} {C D : Ideal O} {hC : Supported C} {hD : Supported D}
  {U : Finset (CommonIndex C D)} {τ : RayFourExpansion.RayCharacter→ Character}
  (hf : Family η C D hC hD U τ)
  (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (R : ℝ) (rows : Finset O)
  (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ)
  (hne : physicalBlock η t S β C D hC hD U R rows W K n≠0)

include hf hK hne in
theorem actual_family_conductor (χ : RayFourExpansion.RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm :=
  (hf.physical_budget t S β R rows W K hK n hne χ).1

include hne in
theorem actual_retained_witness : ∃z : O,
    retainedWeight R (normValue ((commonFrequencyGenerator C D*
      nonunitFrequencyGenerator C D U)*z))≠0 := by
  obtain ⟨z,hz,_,_,_⟩ := physicalBlock_live_dyadic_witness η t S β C D hC hD U
    R rows W K n hne
  exact ⟨z,liveRows_weight C D U R rows z hz⟩

include hf hK hne in
theorem actual_retainedState_width (Z Bmask : ℝ) (hZ : 1< Z)
    (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏p∈U,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨z,hz⟩ := actual_retained_witness t S β R rows W K n hne
  have hU : (∏p∈U,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (commonPrime_supported_ideal C D hC p).1)
  exact retained_log_budget η (τ χ) _ _ z _ hU
    (actual_family_conductor hf t S β R rows W K hK n hne χ) R Z hZ hz

include hf in
theorem actual_nonexceptional_keep (Z Bmask : ℝ) (hZ : 1< Z)
    (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (m z : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m) :
    CenteredMomentRestrictedEnergy.nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).radial.keep z := by
  rw [retainedState_keep]
  exact hf.nonexceptional_iff χ Q m z hm hml hm2

include hf in
theorem actual_sourceRadial_eq (Z Bmask : ℝ) (hZ : 1< Z)
    (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m) :
    CenteredMomentSecondOriginalChildren.sourceRadial
      (CenteredMomentRestrictedEnergy.nonexceptional η χ Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (retainedScale R C D U) (zero_lt_one.trans_le (le_max_left _ _))
      (fun _ => ballProfile_nonneg _) =
      (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).radial := by
  have he : CenteredMomentRestrictedEnergy.nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) =
      daughterKeep (τ χ) Q P := by
    funext z
    exact propext (actual_nonexceptional_keep hf R Z Bmask hZ χ Q P hP hPN m z hm hml hm2)
  unfold CenteredMomentSecondOriginalChildren.sourceRadial retainedState daughterState
  rw [he]

end Actual

theorem actual_main_retainedState_width
    (η₀ η₁ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK₀ : 0< K₀) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁ => p.val) E*
        activeConductor C₁ D₁})
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayFourExpansion.RayCharacter→ Character)
    (hf : Family η₁ C D hC hD U τ)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ)
    (Bmask : ℝ) (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁ => p.val) E}) K₀ V Z
    let Kmain := CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z d k c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C₁.absNorm:ℝ))^2/Kmain) Z ξ
    physicalBlock η₁ t S β C D hC hD U R rows W K n≠0 →
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏p∈U,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hne
  obtain ⟨z,hz⟩ := actual_retained_witness t S β _ rows W K n hne
  have hU : (∏p∈U,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (commonPrime_supported_ideal C D hC p).1)
  exact Cycle61FinalRadius.actual_main_final_width η₀ η₁ (τ χ) C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b N hK₀ hV hZ hb hmod _ _ z _ hU
    (actual_family_conductor hf t S β _ rows W K hK n hne χ) hz
end
end OAI.SevenEighths.Cycle61FinalNatural
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_retainedState_width
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_nonexceptional_keep
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_main_retainedState_width
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_sourceRadial_eq
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_partRows_majorized
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_source_puncture

end
/- END ORIGINAL Cycle61.Physical.FinalNatural.State -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRowState; sha256 446fc3e7d236fb9319df0fc3da9038117398413505f2b86a9c3bd819222eb910 -/
section
                                                       
                                          

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSectorLocalization CenteredMomentSupport
open Cycle61FinalNatural Cycle61Moment
local notation "O" => HeckeFamily.O

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem actual_second_live_correlation (s : Label→ SecondBlockSource)
    (r : secondLiveRows s) :
    idealCorrelation (s r.val.1).C (s r.val.1).D (s r.val.1).hC (s r.val.1).hD
      ((s r.val.1).frequency*r.val.2.2.2.val)≠0 :=
  right_ne_zero_of_mul (Finset.mem_filter.mp r.property).2.2.2

/-- Every retained physical row supplies the character conductor cap.
Cancellation of its containing block is irrelevant to this pointwise gate. -/
theorem actual_second_live_conductor (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block)) (χ : RayCharacter) :
    ((d r.val.1).τ χ).modulus.absNorm≤(d r.val.1).input.η.modulus.absNorm*fixedFactor*
      (∏P∈(d r.val.1).inactive,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D
          (d r.val.1).inactive}).absNorm := by
  apply (d r.val.1).rowBudget
    (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive*r.val.2.2.2.val) _ χ
  simpa only [SecondInputDatum.block,originalSecondBlock,SecondBlockSource.frequency,mul_assoc]
    using actual_second_live_correlation (fun l=>(d l).block) r

/-- Width admissibility now follows from the actual retained row and its
actual character family, without a nonzero-whole-block assumption. -/
theorem actual_second_live_state_width (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1< Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      Real.logb Z v.radius+Real.logb Z (v.input.η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  dsimp only
  rw [retainedState_width]
  have hU : (∏p∈(d r.val.1).inactive,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _=>(commonPrime_supported_ideal _ _ (d r.val.1).hC p).1)
  exact retained_log_budget _ _ _ _ r.val.2.2.2.val _ hU
    (actual_second_live_conductor d r χ) _ _ hZ
    (actual_second_live_retained_weight (fun l=>(d l).block) r.val r.property)


/-- The actual row lies in the plateau of the retained ball profile. -/
theorem actual_second_live_state_majorant (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1< Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let v := d r.val.1
    let st := retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive
    1≤(st.radial.profile (‖eisEmbedding r.val.2.2.2.val‖^2/st.radial.scale)).re := by
  dsimp only
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact Cycle61FinalRadius.actual_retained_majorant _ _ _ r.val.2.2.2.val
    (actual_second_live_retained_weight (fun l=>(d l).block) r.val r.property)

/-- The nonexceptional branch supplies the exact natural-state keep gate
and a nonvanishing radial value used by high-source admissibility. -/
theorem actual_second_live_state_admission (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1< Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η χ Q m
      (d r.val.1).block.frequency r.val.2.2.2.val) :
    let v := d r.val.1
    let st := retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive
    st.radial.keep r.val.2.2.2.val ∧
      st.radial.profile (‖eisEmbedding r.val.2.2.2.val‖^2/st.radial.scale)≠0 := by
  dsimp only
  refine ⟨(actual_nonexceptional_keep (d r.val.1).family _ Z Bmask hZ χ Q P hP hPN
    m _ hm hml hm2).mp hkeep,?_⟩
  have hp := actual_second_live_state_majorant d r Z Bmask hZ χ Q P hP hPN
  dsimp only at hp
  intro hz
  rw [hz] at hp
  norm_num at hp

/-- The right column uses the reflected row, with the same ball majorant
but its own ray character and puncture. -/
theorem actual_second_reflected_state_admission (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1< Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η χ Q m
      (d r.val.1).block.frequency (-r.val.2.2.2.val)) :
    let v := d r.val.1
    let st := retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive
    st.radial.keep (-r.val.2.2.2.val) ∧
      st.radial.profile (‖eisEmbedding (-r.val.2.2.2.val)‖^2/st.radial.scale)≠0 := by
  dsimp only
  refine ⟨(actual_nonexceptional_keep (d r.val.1).family _ Z Bmask hZ χ Q P hP hPN
    m _ hm hml hm2).mp hkeep,?_⟩
  have hp := actual_second_live_state_majorant d r Z Bmask hZ χ Q P hP hPN
  dsimp only at hp
  rw [map_neg,norm_neg]
  intro hz
  rw [hz] at hp
  norm_num at hp

/-- The actual live row inherits the six-amplifier width saving from the
first main radius. This uses the row conductor budget, so a cancelled
physical block does not invalidate admission. -/
theorem actual_second_live_main_width (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (η₀ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK₀ : 0< K₀) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : (d r.val.1).input.η.modulus=η₀.modulus*
      Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E*
        activeConductor C₁ D₁})
    (Bmask : ℝ) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let e := Real.logb Z (D₁.absNorm:ℝ)
    let k := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E}) K₀ V Z
    let Kmain := CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z e k c (3*a) δ reserve
    (d r.val.1).radius=CenteredMomentSectorLocalization.frequencyRadius
      ((b^N*V/(C₁.absNorm:ℝ))^2/Kmain) Z ξ →
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-max (c-e) 0-6*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hradius
  have hw := actual_second_live_state_width d r Z Bmask hZ χ Q P hP hPN
  have hr := Cycle61FinalRadius.main_inverse_radius_log η₀ (d r.val.1).input.η
    C₁ D₁ hC₁ hD₁ heq E K₀ V Z a δ reserve ξ b N hK₀ hV hZ hb hmod
  dsimp only at hw hr
  rw [hradius] at hw ⊢
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_correlation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_conductor
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_state_width

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_state_majorant
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_state_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_main_width

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_reflected_state_admission

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRowState -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondOrientedWidth; sha256 199e9a02c5edc451e06448df9f98586b967c3116ff06b94bdf03cdb5ee246ed2 -/
section
                                                  
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonical CenteredMomentSecondRetainedWidth
open Cycle61FinalNatural
open RayFourExpansion CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

theorem main_inverse_radius_log_oriented (reflected : Bool) (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kmain := mainCommonRadius Z d K0 c (3*a) δ reserve
    Real.logb Z (frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ)+
      Real.logb Z (τ.modulus.absNorm:ℝ) =
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve+
        Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hr := main_fourier_frequency_log reflected C D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
    hC.1 hD.1 (subsetGenerator_supported C D hC E).1 heq
    K V Z (3*a) δ reserve ξ b N hK hV hZ hb
  have hw := CenteredMomentFirstMixedNormalizationActual.actual_reference_width
    η τ C D hC E K Z hK hZ hmod
  dsimp only at hr
  linarith

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem actual_second_live_main_width_oriented (reflected : Bool) (d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (η₀ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK₀ : 0< K₀) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : (d r.val.1).input.η.modulus=η₀.modulus*
      Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E*
        activeConductor C₁ D₁})
    (Bmask : ℝ) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let c := Real.logb Z ((if reflected then D₁ else C₁).absNorm:ℝ)
    let e := Real.logb Z ((if reflected then C₁ else D₁).absNorm:ℝ)
    let k := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁=>p.val) E}) K₀ V Z
    let Kmain := CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z e k c (3*a) δ reserve
    (d r.val.1).radius=CenteredMomentSectorLocalization.frequencyRadius
      ((b^N*V/((if reflected then D₁ else C₁).absNorm:ℝ))^2/Kmain) Z ξ →
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-max (c-e) 0-6*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hradius
  have hw := actual_second_live_state_width d r Z Bmask hZ χ Q P hP hPN
  have hr := main_inverse_radius_log_oriented reflected η₀ (d r.val.1).input.η
    C₁ D₁ hC₁ hD₁ heq E K₀ V Z a δ reserve ξ b N hK₀ hV hZ hb hmod
  dsimp only at hw hr
  rw [hradius] at hw ⊢
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_inverse_radius_log_oriented
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_main_width_oriented

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondOrientedWidth -/
