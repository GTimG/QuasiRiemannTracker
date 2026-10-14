/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B105
import Candidate.Bundles.B109
import Candidate.Bundles.B110
import Candidate.Bundles.B111
import Candidate.Bundles.B113
import Candidate.Bundles.B143
import Candidate.Bundles.B173
import OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondWeightedCommon; sha256 89a9922719b3f47be1e328d0e86105858a281175b3f2c4e741de26aa239470a8 -/
section
                                                         
                                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
local instance secondWeightedSelectionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Keep the actual scalar and common-ideal normalization inside the joint
energy. Only the uniformly bounded allocation mass is taken outside. -/
theorem actual_second_weighted_common_selection {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k)) (C R : κ→ Ideal O) (Ds : κ→ Finset (Ideal O))
      (z : κ→ O) (scalar : κ→ℂ) (E : ℝ),
      (∀k∈rows,(s k).upper≤ b) → (∀k∈rows,C k≠0) →
      (∀S : Finset rows,
        ∀pick : (k : S)→ actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,commonScalar (s k.val.val) (C k.val.val) (R k.val.val) (pick k)≠0) →
        (∑k : S,(‖scalar k.val.val‖^2*(∏i,(s k.val.val).M i)^2*((C k.val.val).absNorm:ℝ)^(ε-1))*
          (∑L∈Ds k.val.val,
          ∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
            retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k))
              L a (z k.val.val)))≤ E) →
      (∑k∈rows,‖scalar k‖^2*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤
        K*E := by
  obtain ⟨K,hK,hbound⟩ := uniform_common_scalar_mass (Fintype.card α) b ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R Ds z scalar E hupper hC hjoint
  let mass (k : rows) := (∏i,(s k.val).M i)^2*((C k.val).absNorm:ℝ)^(ε-1)
  have hmpos (k : rows) : 0< mass k := by
    have hp : 0<∏i,(s k.val).M i := Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one ((s k.val).M_ge_one i))
    have hn := CenteredMomentFirstScale.norm_pos (C k.val) (hC k.val k.property)
    dsimp [mass]
    exact mul_pos (sq_pos_of_pos hp) (Real.rpow_pos_of_pos hn _)
  let cost (k : rows)(B : actualAllocations (s k.val).pools (C k.val)) :=
    ∑L∈Ds k.val,∑a∈(commonData (s k.val) (C k.val) (R k.val) B).toSource.active L,
      retainedAllocationCost (commonData (s k.val) (C k.val) (R k.val) B) L a (z k.val)
  have hcpos (k : rows)(B : actualAllocations (s k.val).pools (C k.val)) : 0≤ cost k B :=
    Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>retained_allocation_cost_nonneg _ _ _ _))
  have hh:=joint_supported_weighted_selection
    (fun (k : rows)(B : actualAllocations (s k.val).pools (C k.val))=>
      (((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)/mass k)
    (fun (k : rows)(B : actualAllocations (s k.val).pools (C k.val))=>
      (‖scalar k.val‖^2*mass k)*cost k B)
    K E hK.le (fun k _=>div_nonneg (by positivity) (hmpos k).le)
    (fun k B=>mul_nonneg (mul_nonneg (sq_nonneg _) (hmpos k).le) (hcpos k B))
    (by
      intro k
      rw [←Finset.sum_div,←Finset.mul_sum]
      apply (div_le_iff₀ (hmpos k)).mpr
      simpa only [mass,mul_assoc] using hbound (ι:=slots k.val) (by simpa using Finset.card_le_univ (slots k.val))
        (s k.val) (hupper k.val k.property) (C k.val) (R k.val) (hC k.val k.property))
    (by
      intro S pick hne
      simpa only [mass,cost,mul_assoc] using hjoint S pick (fun k hc=>hne k (by simp [hc])))
  have hcancel (k : rows)(B : actualAllocations (s k.val).pools (C k.val)) :
      (((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)/mass k*
        ((‖scalar k.val‖^2*mass k)*cost k B)=
      (‖scalar k.val‖^2*((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*
        ‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)*cost k B := by
    field_simp [(hmpos k).ne']
  simp_rw [hcancel] at hh
  apply le_trans (le_of_eq ?_) hh
  dsimp only [cost]
  rw [Finset.sum_coe_sort rows (fun k=>∑B : actualAllocations (s k).pools (C k),
    (‖scalar k‖^2*((actualAllocations (s k).pools (C k)).card:ℝ)*
      ‖commonScalar (s k) (C k) (R k) B‖^2)*
    (∑L∈Ds k,∑a∈(commonData (s k) (C k) (R k) B).toSource.active L,
      retainedAllocationCost (commonData (s k) (C k) (R k) B) L a (z k)))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [commonRetainedCost,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_weighted_common_selection

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondWeightedCommon -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighColumn; sha256 16738ccccec06915b05ec8d94ccccf4dde8cd49dc31da63cabf477932f3f9c51 -/
section
                                                      
                                                        
                                       

set_option autoImplicit false
set_option maxHeartbeats 6000000
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

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

/-- Real physical weights remain inside supported common-allocation selection. -/
theorem high_real_common_selection {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ)(hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k))(C R : κ→ Ideal O)(Ds : κ→ Finset (Ideal O))
      (z : κ→ O)(weight : κ→ℝ)(E : ℝ),
      (∀k,0≤ weight k) → (∀k∈rows,(s k).upper≤ b) → (∀k∈rows,C k≠0) →
      (∀S : Finset rows,∀pick : (k : S)→ actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,frozenCoefficient (pick k).val (C k.val.val) (R k.val.val)
          (s k.val.val).ν (s k.val.val).W (s k.val.val).P≠0) →
        (∑k : S,(weight k.val.val*(∏j,(s k.val.val).M j)^2*((C k.val.val).absNorm:ℝ)^(ε-1))*
          ∑L∈Ds k.val.val,∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
            retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)) L a (z k.val.val))≤ E) →
      (∑k∈rows,weight k*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤ K*E := by
  obtain ⟨K,hK,hcommon⟩:=actual_second_weighted_common_selection (α:=α) b ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R Ds z weight E hw hupper hC hjoint
  let scalar:=fun k=>(Real.sqrt (weight k):ℂ)
  have heq (k : κ) : ‖scalar k‖^2=weight k := by
    dsimp only [scalar]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw k)]
  have hh:=hcommon rows slots s C R Ds z scalar E hupper hC
    (fun S pick hne=>by
      simp only [heq]
      exact hjoint S pick (fun k=>right_ne_zero_of_mul (hne k)))
  simpa only [heq] using hh

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


/-- Actual normalized columns after supported allocation selection. Zero-shell
and height gates remain literal partition data, without an energy premise. -/
theorem actual_geometry_selected_high_columns {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width : ℝ) (i : ℕ),
      167/200 ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      Function.Injective key →
      ∀labels : Finset κ,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, β ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      let R₂:=fun l=>(datum (row l).val.1).R
      let outer:=fun l=>Z^(-ampExponent)*
        (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
          (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
        normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
      let hE : ∀l,Supported (E l):=fun l=>by
        dsimp only [E]; split <;> first | exact (datum (row l).val.1).hD | exact (datum (row l).val.1).hC
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
          (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2))≤
      Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_literal_high_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨Kextract,hKextract,hextract⟩:=actual_uniform_second_column_extraction (α:=α) ε hε
  obtain ⟨Kcommon,hKcommon,hcommon⟩:=high_real_common_selection.{0,0} (α:=α) b ε hε
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩:=hhigh P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,Kextract*Kcommon,hF,hCprofile,hC,mul_pos hKextract hKcommon,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i
    hβ hβ' hKcontrol hT hwidthbin hinj labels A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E R₂ outer hE seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
  let coeff:=fun l=>Z^(-ampExponent)*
    (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
    (normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive/
      Z^(Real.logb Z ((E l).absNorm:ℝ)))
  have hZ : 1< Z:=(by norm_num : (1:ℝ)<2).trans_le he.1
  have hZpos : 0< Z:=zero_lt_one.trans hZ
  let mass:=fun l=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)
  let source:=fun l=>withHeight (firstChild l) (st l).character (t l)
  let rhs:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
    (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
      Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass))
  have hrhs : 0≤ rhs := by
    dsimp only [rhs]
    exact mul_nonneg (mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Nat.cast_nonneg _)) (by positivity)
  have houter (l : κ) : 0≤ outer l := by
    dsimp only [outer]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hZpos.le _)
      (div_nonneg (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*ampExponent)
        reserveShift hZpos _).le (volume_pos (firstChild l)).le))
      (normalizer_pos _ _ (datum (row l).val.1).hC _).le
  have hmass (l : κ) : 0≤ mass l :=geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l)
  have hprod (l : κ) : (∏j,(source l).M j)^2≤ Cs^(2*N) := by
    have hp : (∏j,(source l).M j)≤ Cs^N := by
      calc
        _≤∏_j : liveIndices (B₁ l).val,Cs:=Finset.prod_le_prod₀
          (fun j _=>zero_le_one.trans ((source l).M_ge_one j)) (fun j _=>hM j.val)
        _=Cs^(Fintype.card (liveIndices (B₁ l).val)):=by simp
        _≤ Cs^N:=pow_le_pow_right₀ hCs ((live_card_le (B₁ l).val).trans hcard)
    exact (pow_le_pow_left₀ (Finset.prod_nonneg (fun j _=>zero_le_one.trans ((source l).M_ge_one j))) hp 2).trans_eq
      (by rw [←pow_mul]; congr 1; omega)
  have hn (l : κ) : 0<((E l).absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ (hE l).1
  have hcoeff (l : κ) : outer l*((E l).absNorm:ℝ)^(ε-1)=coeff l*((E l).absNorm:ℝ)^ε := by
    have heq : Z^(Real.logb Z ((E l).absNorm:ℝ))=((E l).absNorm:ℝ):=Real.rpow_logb hZpos hZ.ne' (hn l)
    dsimp only [coeff,outer,E]
    rw [Real.rpow_sub (hn l),Real.rpow_one]
    rw [heq]
    ring
  have hcommonBound : (∑l∈labels,mass l*outer l*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l))≤
      Kcommon*(Cs^(2*N)*Z^(B*ε)*rhs) := by
    apply hcommon labels (fun l=>liveIndices (B₁ l).val) source E R₂ Ds z (fun l=>mass l*outer l)
      (Cs^(2*N)*Z^(B*ε)*rhs) (fun l=>mul_nonneg (hmass l) (houter l))
      (fun _ _=>hupper) (fun l _=>(hE l).1)
    intro S pick hne
    by_cases hempty : S.Nonempty
    · let _ : Nonempty ↥S:=Finset.nonempty_coe_sort.mpr hempty
      have hselected:=he.2 reflected second s hη R seed W D ξ hK bin
        (fun l : S=>column l.val.val) datum first (fun l=>row l.val.val)
        (fun l=>hparent l.val.val) (fun l=>hfirst l.val.val) (fun l=>hR l.val.val) (fun l=>ψ l.val.val)
        β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i
        hβ hβ' hKcontrol hT hwidthbin
        (fun j k heq=>Subtype.ext (Subtype.ext (hinj heq))) Finset.univ
        (fun l _=>hq l.val.val l.val.property) hseed hs₁ hs₂ hsource hlower
        hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap
        (fun l _=>hnorm l.val.val l.val.property) (fun l _=>hradius l.val.val l.val.property)
        (fun l=>st l.val.val) (fun l=>hQM l.val.val) (fun l=>hQη l.val.val)
        (fun l=>z l.val.val) (fun l=>hz l.val.val)
        (fun l=>hchar l.val.val) (fun l=>hpuncture l.val.val) (fun l=>hrow l.val.val)
        (fun l _=>hzero l.val.val l.val.property) (fun l _=>hsupport l.val.val l.val.property)
        hi hcard hM hb₁ hb₂ hupper hwin
        (fun l=>B₁ l.val.val) (fun l=>t₁ l.val.val) (fun l _=>hf₁ l.val.val l.val.property)
        pick (fun l=>t l.val.val) w σ v θ (fun l=>p l.val.val) (fun l=>Ds l.val.val) cap
        hcap hmatches hscales hpadallow (fun l _=>hne l)
        (fun l _=>hwidth l.val.val l.val.property) (fun l _=>hradial l.val.val l.val.property)
        (fun l _=>hzeroUpper l.val.val l.val.property) hw hwr hσlo hσhi
        (fun l _=>hheight l.val.val l.val.property) (fun l _=>hplainheight l.val.val l.val.property)
        (fun l _=>hW l.val.val l.val.property) (fun l _=>hDs l.val.val l.val.property)
        (fun l _=>hdyad l.val.val l.val.property) (fun l _=>hcontrol l.val.val l.val.property) hledger
      let shell:=fun l : S=>∑L∈Ds l.val.val,∑a∈(commonData (source l.val.val) (E l.val.val) (R₂ l.val.val) (pick l)).toSource.active L,
        retainedAllocationCost (commonData (source l.val.val) (E l.val.val) (R₂ l.val.val) (pick l)) L a (z l.val.val)
      have hshell (l : S) : 0≤ shell l:=Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>retained_allocation_cost_nonneg _ _ _ _))
      have hncap (l : S) : ((E l.val.val).absNorm:ℝ)^ε≤ Z^(B*ε):=
        (Real.rpow_le_rpow (hn l.val.val).le (by
          cases second
          · exact (hnorm l.val.val l.val.property).1
          · exact (hnorm l.val.val l.val.property).2) hε.le).trans_eq (Real.rpow_mul hZpos.le _ _).symm
      calc
        _≤∑l : S,(Cs^(2*N)*Z^(B*ε))*(mass l.val.val*coeff l.val.val*shell l) := by
          apply Finset.sum_le_sum
          intro l _
          have hc : 0≤ coeff l.val.val := by
            have heq : coeff l.val.val=outer l.val.val/Z^(Real.logb Z ((E l.val.val).absNorm:ℝ)):=by
              dsimp only [coeff,outer];ring
            rw [heq]
            exact div_nonneg (houter _) (Real.rpow_nonneg hZpos.le _)
          have hh:=mul_le_mul (hprod l.val.val) (hncap l)
            (Real.rpow_nonneg (hn l.val.val).le _) (by positivity : 0≤ Cs^(2*N))
          have hp:=mul_le_mul_of_nonneg_right hh (mul_nonneg (mul_nonneg (hmass l.val.val) hc) (hshell l))
          calc
            _=(∏j,(source l.val.val).M j)^2*(mass l.val.val*(outer l.val.val*((E l.val.val).absNorm:ℝ)^(ε-1))*shell l):=by ring
            _=(∏j,(source l.val.val).M j)^2*(mass l.val.val*(coeff l.val.val*((E l.val.val).absNorm:ℝ)^ε)*shell l):=by rw [hcoeff]
            _≤ _:=by convert hp using 1; ring
        _=(Cs^(2*N)*Z^(B*ε))*(∑l : S,mass l.val.val*coeff l.val.val*shell l):=(Finset.mul_sum ..).symm
        _≤(Cs^(2*N)*Z^(B*ε))*rhs:=mul_le_mul_of_nonneg_left hselected (by positivity)
    · let _ : IsEmpty ↥S:=⟨fun l=>hempty ⟨l.val,l.property⟩⟩
      simp only [Finset.univ_eq_empty,Finset.sum_empty]
      positivity
  calc
    _≤∑l∈labels,mass l*outer l*(Kextract*(2*T)^ε*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l)) := by
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hmass l) (houter l))
      calc
        _≤∑L∈Ds l,Kextract*(2*T)^ε*commonRetainedCost (source l) (E l) (R₂ l) L (z l) := by
          apply Finset.sum_le_sum
          intro L hL
          exact (hextract (liveIndices (B₁ l).val) (source l) (E l) (hE l) (R₂ l) (seed₂ l) L
            (hseed₂ l hl) (hDs l hl L hL) (z l)).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg _) (hdyad l hl L hL).2.le hε.le) hKextract.le)
              (common_retained_cost_nonneg _ _ _ _ _))
        _=Kextract*(2*T)^ε*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l):=(Finset.mul_sum ..).symm
    _=(Kextract*(2*T)^ε)*(∑l∈labels,mass l*outer l*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _≤(Kextract*(2*T)^ε)*(Kcommon*(Cs^(2*N)*Z^(B*ε)*rhs)):=
      mul_le_mul_of_nonneg_left hcommonBound (by positivity)
    _=_:=by dsimp only [rhs];ring

/-- The actual Mellin window splits at a literal height cutoff. Both
integrals are retained, including the unrestricted complementary tail. -/
theorem actual_high_column_mellin_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι)(E R seed L : Ideal O)(hE : Supported E)(η : Character)
    (t θ X Z τ : ℝ)(hX : 0< X)(V : ℝ→ℂ)
    (hc : HasCompactSupport V)(hs : ContDiff ℝ ∞ V)(z : O) :
    let f:=fun u : ℝ=>columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
      normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) E hE R seed L z
    let small:= {u : ℝ | 1+‖u‖≤ Z^τ}
    windowColumn s E hE R seed L η t θ X V z=
      (∫u in small,f u)+(∫u in smallᶜ,f u) := by
  intro f small
  have hsmall : MeasurableSet small:=
    (isClosed_le (continuous_const.add continuous_norm) continuous_const).measurableSet
  have hi : Integrable f:=actual_window_column_integrable s E hE R seed L η t θ X hX V hc hs z
  rw [actual_window_column_integral s E hE R seed L η t θ X hX V hc hs z]
  exact (integral_add_compl hsmall hi).symm

/-- Finite physical weights remain inside both genuine Mellin pieces.
This truncation inequality introduces no selected energy premise. -/
theorem actual_high_weighted_mellin_split {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ)(slots : κ→ Finset α)(s : (k : κ)→ Input (slots k))
    (E R seed : κ→ Ideal O)(hE : ∀k,Supported (E k))(Ds : κ→ Finset (Ideal O))
    (η : κ→ Character)(t θ X : κ→ℝ)(hX : ∀k,0< X k)(z : κ→ O)
    (weight : κ→ℝ)(hw : ∀k,0≤ weight k)(Z τ : ℝ)
    (V : ℝ→ℂ)(hc : HasCompactSupport V)(hs : ContDiff ℝ ∞ V) :
    let f:=fun k L u=>columnDensity V hc hs u*logPhase (θ k-u) (Real.log (X k))*
      normalizedColumn (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
        (E k) (hE k) (R k) (seed k) L (z k)
    let small:= {u : ℝ | 1+‖u‖≤ Z^τ}
    (∑k∈rows,weight k*∑L∈Ds k,‖windowColumn (s k) (E k) (hE k) (R k) (seed k) L
      (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
    2*(∑k∈rows,weight k*∑L∈Ds k,‖∫u in small,f k L u‖^2)+
      2*(∑k∈rows,weight k*∑L∈Ds k,‖∫u in smallᶜ,f k L u‖^2) := by
  intro f small
  have hsplit (k : κ)(L : Ideal O) :
      windowColumn (s k) (E k) (hE k) (R k) (seed k) L (η k) (t k) (θ k) (X k) V (z k)=
      (∫u in small,f k L u)+(∫u in smallᶜ,f k L u):=
    actual_high_column_mellin_split (s k) (E k) (R k) (seed k) L (hE k) (η k)
      (t k) (θ k) (X k) Z τ (hX k) V hc hs (z k)
  calc
    _≤∑k∈rows,weight k*∑L∈Ds k,
      (2*‖∫u in small,f k L u‖^2+2*‖∫u in smallᶜ,f k L u‖^2) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (hw k)
      apply Finset.sum_le_sum
      intro L _
      rw [hsplit]
      have hadd:=norm_add_le (∫u in small,f k L u) (∫u in smallᶜ,f k L u)
      nlinarith [norm_nonneg ((∫u in small,f k L u)+(∫u in smallᶜ,f k L u)),
        norm_nonneg (∫u in small,f k L u),norm_nonneg (∫u in smallᶜ,f k L u),
        sq_nonneg (‖∫u in small,f k L u‖-‖∫u in smallᶜ,f k L u‖)]
    _=2*(∑k∈rows,weight k*∑L∈Ds k,‖∫u in small,f k L u‖^2)+
        2*(∑k∈rows,weight k*∑L∈Ds k,‖∫u in smallᶜ,f k L u‖^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum,mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;>
        apply Finset.sum_congr rfl <;> intro L _ <;> ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_real_common_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_high_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_column_mellin_split
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_weighted_mellin_split

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighColumn -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseControl; sha256 6ea662f99e01827529df452d23b4d2bbd8c7c6ad71c47c25e0df74a888e4e1ca -/
section
                                                     
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

/-- Fixed coefficient cost for the coarse tail. Its large size is harmless:
it is chosen before all scales, rows, allocations and heights. -/
def coarseFixedControl (N : ℕ)(Cs b bs : ℝ) : ℝ :=
  (2*(bs*bs))*(Cs^N)^2*((128*bs)^2*(128*b*Cs)^N)^2*2

lemma coarse_fixed_control_pos (N : ℕ)(Cs b bs : ℝ)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs) : 0< coarseFixedControl N Cs b bs := by
  unfold coarseFixedControl
  positivity

/-- Actual scale and coefficient gates imply a uniform coarse polynomial
bound; this does not assume an analytic moment estimate. -/
theorem actual_coarse_control_fixed {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b bs cap Z B₁ B₂ : ℝ)(hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)
    (hcap : 0≤ cap)(hZ : 1≤ Z)(hB₁ : 0≤ B₁)(hB₂ : 0≤ B₂)
    (s : Data ι)(hcard : Fintype.card ι≤ N)(hM : ∀j,s.M j≤ Cs)
    (hhi : ∀j,s.hi j≤ b)(hb₁ : s.b₁≤ bs)(hb₂ : s.b₂≤ bs)
    (hscales : ∀second j,Cycle61.Physical.sourcePlainScales s.toSource second j≤ Z^cap)
    (hP : ∀j,s.P j≤ Z^cap) :
    coarseAllocationControl s B₁ B₂≤
      coarseFixedControl N Cs b bs*(B₁*B₂)^2*Z^(((N:ℝ)+2)*cap) := by
  have hz : 0< Z := lt_of_lt_of_le (by norm_num) hZ
  have hzcap : 1≤ Z^cap := Real.one_le_rpow hZ hcap
  have hm0 : ∀j,0≤ s.M j := fun j=>zero_le_one.trans (s.M_ge_one j)
  have hpM : (∏j,s.M j)≤ Cs^N := by
    calc
      _≤∏_j : ι,Cs := Finset.prod_le_prod₀ (fun j _=>hm0 j) (fun j _=>hM j)
      _=Cs^(Fintype.card ι) := by simp
      _≤ Cs^N := pow_le_pow_right₀ hCs hcard
  have hfac0 : ∀j,0≤128*max 1 (s.hi j)*s.M j := fun j=>mul_nonneg (by positivity) (hm0 j)
  have hpF : (∏j,128*max 1 (s.hi j)*s.M j)≤(128*b*Cs)^N := by
    calc
      _≤∏_j : ι,128*b*Cs := Finset.prod_le_prod₀ (fun j _=>hfac0 j) (fun j _=>by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (max_le hb (hhi j)) (by norm_num)
        · exact hM j
        · exact hm0 j
        · positivity)
      _=(128*b*Cs)^(Fintype.card ι) := by simp
      _≤ _ := pow_le_pow_right₀ (by nlinarith [mul_le_mul hb hCs (by norm_num : (0:ℝ)≤1) (by linarith : 0≤ b)]) hcard
  have hrow : coarseRowControl s B₁ B₂≤((128*bs)^2*(128*b*Cs)^N)*(B₁*B₂) := by
    unfold coarseRowControl
    calc
      _≤(128*bs*B₁)*(128*bs*B₂)*(128*b*Cs)^N := by
        apply mul_le_mul _ hpF (Finset.prod_nonneg (fun j _=>hfac0 j)) (by positivity)
        apply mul_le_mul
        · gcongr; exact max_le hbs hb₁
        · gcongr; exact max_le hbs hb₂
        · positivity
        · positivity
      _=_ := by ring
  have hsize (second : Bool) : coarseRowSize s second≤ Z^(((N:ℝ)+2)*cap) := by
    have hp : (∏j,max 1 (s.P j))≤(Z^cap)^N := by
      calc
        _≤∏_j : ι,Z^cap := Finset.prod_le_prod₀ (fun _ _=>by positivity)
          (fun j _=>max_le hzcap (hP j))
        _=(Z^cap)^(Fintype.card ι) := by simp
        _≤ _ := pow_le_pow_right₀ hzcap hcard
    unfold coarseRowSize
    calc
      _≤ Z^cap*Z^cap*(Z^cap)^N := by
        apply mul_le_mul _ hp (Finset.prod_nonneg (fun _ _=>by positivity)) (by positivity)
        exact mul_le_mul (max_le hzcap (hscales second 0)) (max_le hzcap (hscales second 1))
          (by positivity) (by positivity)
      _=Z^(((N:ℝ)+2)*cap) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  have hMprod0 : 0≤∏j,s.M j := Finset.prod_nonneg (fun j _=>hm0 j)
  have hrow0 : 0≤ coarseRowControl s B₁ B₂ := by
    unfold coarseRowControl
    exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _=>hfac0 j))
  unfold coarseAllocationControl
  calc
    _≤(2*(bs*bs))*(Cs^N)^2*(((128*bs)^2*(128*b*Cs)^N)*(B₁*B₂))^2*
        (2*Z^(((N:ℝ)+2)*cap)) := by
      apply mul_le_mul _ (by linarith [hsize false,hsize true])
        (add_nonneg (coarse_row_size_nonneg s false) (coarse_row_size_nonneg s true)) (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ hrow0 hrow 2) (sq_nonneg _) (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ hMprod0 hpM 2) (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (max_le hbs hb₁) (max_le hbs hb₂) (by positivity) (by positivity)) (by norm_num)
    _=_ := by unfold coarseFixedControl; ring

/-- The two literal common allocations inherit the coarse bound from the
original input, uniformly in both newly introduced characters and heights. -/
theorem actual_two_common_coarse_control {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b bs cap Z B₁ B₂ : ℝ)(hCs : 1≤ Cs)(hb : 1≤ b)(hbs : 1≤ bs)
    (hcap : 0≤ cap)(hZ : 1≤ Z)(hB₁ : 0≤ B₁)(hB₂ : 0≤ B₂)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(hM : ∀j,s.M j≤ Cs)
    (hupper : s.upper≤ b)(hb₁ : s.b₁≤ bs)(hb₂ : s.b₂≤ bs)
    (hscales : ∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap)
    (hP : ∀j,s.P j≤ Z^cap)
    (C₁ R₁ : Ideal O)(A₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
    (C₂ R₂ : Ideal O)(A₂ : actualAllocations (child s C₁ R₁ A₁ χ₁ t₁).pools C₂)
    (χ₂ : Character)(t₂ : ℝ) :
    coarseAllocationControl
      (commonData (withHeight (child s C₁ R₁ A₁ χ₁ t₁) χ₂ t₂) C₂ R₂ A₂) B₁ B₂≤
      coarseFixedControl N Cs b bs*(B₁*B₂)^2*Z^(((N:ℝ)+2)*cap) := by
  apply actual_coarse_control_fixed N Cs b bs cap Z B₁ B₂ hCs hb hbs hcap hZ hB₁ hB₂
  · exact (live_card_le A₂.val).trans ((live_card_le A₁.val).trans hcard)
  · intro j; exact hM j.val.val
  · intro j; exact (s.upper_ge j.val.val).trans hupper
  · exact hb₁
  · exact hb₂
  · intro second j
    have hn : (1:ℝ)≤(A₂.val (Sum.inr j)).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (alloc_ne (child s C₁ R₁ A₁ χ₁ t₁) C₂ A₂ (Sum.inr j)))
    have hh := actual_child_plain_scale_le s C₁ R₁ A₁ χ₁ t₁ second j
    apply le_trans _ (hh.trans (hscales second j))
    cases second <;> fin_cases j
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).X₁_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).X₂_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).Y₁_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).Y₂_pos.le hn
  · intro j; exact hP j.val.val

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_coarse_control_fixed

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_two_common_coarse_control

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseControl -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseCount; sha256 ea24a33c0a74e6a34f717a538cc9fe05d829c0ff02d7c01c64f93cefa9785454 -/
section
                                      
                                                         
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open Cycle61Moment CenteredMomentFirstAmplificationChoice CenteredMomentAbsoluteEnergy
open CenteredMomentSectorLocalization ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O

/-- A fixed smooth majorant counts all literal lattice rows, independently of
zero detection or Mellin height. -/
theorem coarse_nonzero_lattice_count (X : ℝ)(hX : 1≤ X)
    (rows : Finset NonzeroFrequency)
    (hrows : ∀w∈rows,rawFrequencyNorm w≤ X) :
    (rows.card:ℝ)≤ diagonalControl ballProfile*X := by
  have hX0 : 0< X := by linarith
  let vals := rows.image (fun w=>w.val)
  have hcard : vals.card=rows.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hpoint (z : O)(hz : z∈vals) :
      1≤‖ballProfile (‖eisEmbedding z‖^2/X)‖ := by
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (ballProfile_majorizes X hX0 w.val (hrows w hw)).trans (Complex.re_le_norm _)
  calc
    (rows.card:ℝ) = ∑ _z∈vals,(1:ℝ) := by simp [hcard]
    _ ≤ ∑ z∈vals,‖ballProfile (‖eisEmbedding z‖^2/X)‖ := Finset.sum_le_sum hpoint
    _ ≤ ∑' z : O,‖ballProfile (‖eisEmbedding z‖^2/X)‖ :=
      (radial_norm_summable ballProfile X hX0).sum_le_tsum vals (fun _ _=>norm_nonneg _)
    _ ≤ _ := by simpa only [max_eq_right hX] using radial_weight_lattice_bound_all ballProfile X hX0

/-- Coarse joint cardinality, retaining the same missing-radical fiber count
as the sharp high branch. All constants precede labels and moving data. -/
theorem actual_joint_coarse_row_count (B loss : ℝ)(hB : 0≤ B)(hloss : 0< loss) :
    ∃C : ℝ,0< C ∧ ∀left : Bool,∀u₀ : O,∀unit : FirstSourceLabel→ O,
      ∀Z : ℝ,2≤ Z → ∀m : ℝ,
      ∀labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow label)≤ Z^B) →
      (∀label∈labels,Supported label.val.1.1.1 ∧ label.val.1.1.2≠0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2≠0) →
      (∀label∈labels,primeSupport label.val.1.1.1=primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1=primeSupport label.val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit label.val}*
        firstSourceMissing left label.val.1).absNorm:ℝ)≤ Z^B) →
      (∀label∈labels,(label.val.1.1.1.absNorm:ℝ)≤ Z^B ∧
        (label.val.1.1.2.absNorm:ℝ)≤ Z^B ∧
        (label.val.2.1.1.absNorm:ℝ)≤ Z^B ∧ (label.val.2.1.2.absNorm:ℝ)≤ Z^B) →
      (∀label∈labels,((firstSourceMissing left label.val.1).absNorm:ℝ)≤ Z^m) →
      (labels.card:ℝ)≤ C*Z^(m+B+loss) := by
  obtain ⟨C,hC,hcount⟩ := actual_joint_source_row_count B loss hB hloss
  let D := max 1 (diagonalControl ballProfile)
  have hD : 0< D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro left u₀ unit Z hZ m labels hrowbound hnonzero heq hsupportnorm hnorm hmissing
  let row : NonzeroJointSourceLabel left u₀ unit → NonzeroFrequency := nonzeroJointSourceRow
  have hZ0 : 0< Z := by linarith
  have hd : ((labels.image row).card:ℝ)≤ D*Z^B := by
    apply (coarse_nonzero_lattice_count (Z^B)
      (Real.one_le_rpow (by linarith) hB) (labels.image row) ?_).trans
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · intro w hw
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hw
      exact hrowbound l hl
  have hfiber (w : NonzeroFrequency) (hw : w ∈ labels.image row) :
      ((labels.filter (fun label => row label = w)).card:ℝ) ≤ C*Z^(m+loss) := by
    let fibre := labels.filter (fun label => row label = w)
    have mem_fibre (v : NonzeroJointSourceLabel left u₀ unit) (hv : v ∈ fibre) :
        v ∈ labels ∧ row v = w := by
      simpa only [fibre, Finset.mem_filter] using hv
    have hc := hcount left u₀ unit Z hZ w.val w.property
      (by
        obtain ⟨label,hl,hrow⟩ := Finset.mem_image.mp hw
        have hn := hrowbound label hl
        change ((Ideal.span {jointSourceRow left u₀ unit label.val}).absNorm:ℝ) ≤ Z^B at hn
        have he : jointSourceRow left u₀ unit label.val = w.val := congrArg Subtype.val hrow
        rw [he] at hn
        exact hn)
      m (fibre.image Subtype.val)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        exact congrArg Subtype.val (mem_fibre v hv).2)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnonzero v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact heq v (mem_fibre v hv).1)
      (by
        intro label hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        have he : jointSourceRow left u₀ unit v.val = w.val :=
          congrArg Subtype.val (mem_fibre v hv).2
        simpa only [he] using hsupportnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hnorm v (mem_fibre v hv).1)
      (by intro label hl; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl; exact hmissing v (mem_fibre v hv).1)
    have hinj : Set.InjOn (fun v : NonzeroJointSourceLabel left u₀ unit => v.val)
        (↑fibre : Set (NonzeroJointSourceLabel left u₀ unit)) :=
      fun v _ r _ h => Subtype.ext h
    have hcard : fibre.card ≤ (fibre.image Subtype.val).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv
        exact Finset.mem_image_of_mem _ hv
      · exact hinj
    change (fibre.card:ℝ) ≤ C*Z^(m+loss)
    exact (show (fibre.card:ℝ) ≤ ((fibre.image Subtype.val).card:ℝ) by exact_mod_cast hcard).trans hc
  have he := Finset.card_eq_sum_card_fiberwise
    (fun label (hl : label ∈ labels) => Finset.mem_image_of_mem row hl)
  calc
    _ = ∑w∈labels.image row,((labels.filter (fun label=>row label=w)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑_w∈labels.image row,C*Z^(m+loss) := Finset.sum_le_sum hfiber
    _ = ((labels.image row).card:ℝ)*(C*Z^(m+loss)) := by simp
    _ ≤ (D*Z^B)*(C*Z^(m+loss)) := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = (D*C)*Z^(m+B+loss) := by
      calc
        _ = (D*C)*(Z^B*Z^(m+loss)) := by ring
        _ = _ := by rw [←Real.rpow_add hZ0]; congr 1; ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.coarse_nonzero_lattice_count
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_coarse_row_count

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseCount -/
