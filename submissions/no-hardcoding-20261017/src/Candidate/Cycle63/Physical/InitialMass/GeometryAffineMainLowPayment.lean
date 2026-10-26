/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle63InitialMass
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
open Cycle63FinalNatural Cycle63Moment.LowBranch
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
open Cycle63Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open CenteredMomentNaturalRowSource
open Cycle63InitialSource
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local notation "O" => HeckeFamily.O
local instance geometryAffineMainLowDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

/-- Profiles supply the actual full-source zero gate. -/
theorem affine_main_low_profile_zero (p : Profiles (1/4) (9/4)) (j : Fin 2) : p.profile j 0=0 := by
  by_contra h
  have hh := (p.support j h).1
  norm_num at hh

/-- Only positive fees accompany the single negative low reserve. -/
theorem affine_main_low_target_lower (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ)(ha : 0≤amp)(ho : 0≤omega)(hm : 0≤mesh) :
    -1≤geometryAffineLowTarget g N amp omega mesh := by
  have hq : 0≤Cycle63.Arithmetic.q0 := by linarith [Cycle63.Arithmetic.q0_bounds.1]
  have hmu:=g.μ_pos.le
  have hd:=g.δ_pos.le
  unfold geometryAffineLowTarget
  have hp : 0≤(2*Cycle63.Arithmetic.q0/9)*(omega+g.μ/8) := by positivity
  have hpm : 0≤Cycle63.Arithmetic.q0*mesh := mul_nonneg hq hm
  have hN : 0≤2*g.δ*31*(N:ℝ) := by positivity
  have hs : 0≤3*((N:ℝ)+2)*3*g.δ := by positivity
  have hlow : Cycle63.Arithmetic.lowReserve ≤ 1 := by
    unfold Cycle63.Arithmetic.lowReserve Cycle63.Arithmetic.alpha Cycle63.Optimization.lowReserveWeight
    nlinarith [Cycle63.Arithmetic.q0_bounds.1]
  linarith

set_option linter.unusedVariables false in
set_option linter.defProp false in
set_option maxHeartbeats 160000 in
def GeometryAffineMainLowSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (ηseed : Character)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤mesh)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤mesh)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : Cycle63.CountAffine.windowBottom≤length Z X₁)(hlo₂ : Cycle63.CountAffine.windowBottom≤length Z X₂)
    (hhi₁ : length Z X₁≤Cycle63.CountAffine.plainLengthTop)(hhi₂ : length Z X₂≤Cycle63.CountAffine.plainLengthTop)
    (hslots : Cycle63.Optimization.slotFloor≤∑i,w i ∧ (∑i,w i)≤Cycle63.Optimization.slotTop)
    (hcone : length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B),
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    ∀{Label : Type}[Fintype Label]
      (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
      (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
      (9/4) t (Fintype.card α) hZ bin hz₁ hz₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (g.μ/64) (g.μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      hz₁ hz₂ r.val.2
    ∀(χ₀ : rows→RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    ∃hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∃hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hbeta hβhi
    let firstMass:=fun l=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z (g.μ/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    mainLowPhysicalCompleteCost (Fintype.card α) 1 (1/4) second
      (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
      (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(geometryAffineLowTarget g (Fintype.card α) amp omega mesh)*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

set_option linter.defProp false in
def GeometryAffineMainLowSourceSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Cs Z : ℝ) : Prop :=
  ∀(θ : α→RayQuotient.Characters M H)(η₀ : Character)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    (∀i,0≤w i) → Cycle63.CountAffine.windowBottom≤length Z X₁ → Cycle63.CountAffine.windowBottom≤length Z X₂ →
    length Z X₁≤Cycle63.CountAffine.plainLengthTop → length Z X₂≤Cycle63.CountAffine.plainLengthTop → (∑i,w i)≤Cycle63.Optimization.slotTop →
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z

attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost
set_option maxHeartbeats 180000 in
theorem affine_main_low_spec_of_receipts
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (ηseed : Character)(Cs : ℝ)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ)
    (hω : 0≤frequencyLoss Z 32 (g.μ/64)+g.μ/8 ∧
      frequencyLoss Z 32 (g.μ/64)+g.μ/8≤33*g.μ/128)
    (hcaps : GeometryAffineMainLowSourceSpec (α:=α) M H hH W hW hWs Cs Z)
    (hspec : GeometryAffineLowSelectedSpec (α:=α) M H hH W hbeta g ηseed Cs Sp degreeAll Kall η₀ Q hQM hQ72 Z) :
    GeometryAffineMainLowSpec (α:=α) M H hH W hW hWs hbeta g ηseed Sp degreeAll Kall η₀ Q hQM hQ72 Z := by
  unfold GeometryAffineMainLowSpec
  intro hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh hw hmesh hmeshcap hwm
    hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone s hz₁ hz₂
    Label _ reflected second bin t firstIndex first amp omega hf₁ hinj rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u
  have cap₀:=hcaps θ η₀ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots.2
  obtain ⟨caps,hm⟩:=actual_affine_low_source_gates M H hH η₀ θ W hW hWs w σ freq hσ state p
    tplain X₁ X₂ hX₁ hX₂ Cs hZ hw hslots.2 hhi₁ hhi₂ cap₀
  have hlogs : ∀j,Real.logb Z (s.P j)=w j := by
    intro j
    change Real.logb Z (Z^(w j))=w j
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hsum : (∑j,Real.logb Z (s.P j))=∑j,w j := Finset.sum_congr rfl (fun j _=>hlogs j)
  have hηs : s.η=ηseed := hη
  have hw₁ (j : α) : w j≤1 :=
    (Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)).trans (hslots.2.trans Cycle63.Optimization.slotTop_le_one)
  have hwr (j : α) : w j/31≤1 := by linarith [hw₁ j]
  have hcell:=Cycle63.Moment.originalCell_mem hslots
  have hbetaCell:=Cycle63.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := by
    simpa only [amp,hsum,div_one,one_mul] using (Cycle63.Arithmetic.amp_pos hbetaCell).le
  have hamp : |amp|≤4 := by
    rw [abs_of_nonneg hamp0]
    have h:= (Cycle63.Arithmetic.amp_bounds hbetaCell).2.trans (by linarith only [Cycle63.Optimization.amplifierCap_bounds.2] :
      Cycle63.Optimization.amplifierCap≤4)
    simpa only [amp,hsum,div_one,one_mul] using h
  have homega : |omega|≤4 := by
    rw [abs_of_nonneg hω.1]
    exact hω.2.trans (by linarith [g.μ_cap])
  have htarget:=affine_main_low_target_lower g (Fintype.card α) amp omega mesh hamp0 hω.1 hmesh
  unfold GeometryAffineLowSelectedSpec at hspec
  have hb:=hspec (Label:=Label) hZ s p caps θ w σ freq hm hηs height mesh hw
    (fun j=>(hwm j).trans hmeshcap) hwr hmesh hwm hσ hheight hfreq hT hβhi
    (by simpa only [hsum] using hslots) (by
      change length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B
      simpa only [hsum] using hcone)
    reflected second bin t firstIndex hamp0 hamp homega htarget hf₁ hinj χ₀ m hm₀ hml hm₂ Ψ t₀ u
  exact hb

attribute [local irreducible] GeometryAffineMainLowSpec GeometryAffineLowSelectedSpec
attribute [local irreducible] actual_affine_low_selected_payment
set_option maxHeartbeats 180000 in
def actual_affine_main_low_payment
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(ηseed : Character)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0) :
    ΣCs : ℝ,ΣdegreeAll : Finset α→ℕ,ΣSp : Finset α→Finset (ℕ×ℕ),
      PLift (1≤Cs ∧ ∀T,(0,0)∈Sp T) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
        ΣKall : Finset α→ℝ,PLift ((∀T,0<Kall T) ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          ∀T : Finset α,GeometryAffineMainLowSpec (α:=T) M H hH W hW.continuous hWs hbeta g
            ηseed (Sp T) (degreeAll T) (Kall T) η₀ Q hQM hQ72 Z)) := by
  let sources:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW.continuous hWs
  let Cs:=Classical.choose sources
  have hCs:=(Classical.choose_spec sources).1
  have hsources:=(Classical.choose_spec sources).2
  let ks (T : Finset α):=actual_affine_low_selected_payment (α:=T) M H hH W hWs hW hbeta g
    ηseed Cs hCs ηcoarse u₀ F₀ R₀ hu₀
  refine ⟨Cs,(fun T=>(ks T).1),(fun T=>(ks T).2.1),PLift.up ⟨hCs,fun T=>(ks T).2.2.1.down⟩,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let kc (T : Finset α):=(ks T).2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨(fun T=>(kc T).1),PLift.up ⟨(fun T=>(kc T).2.down.1),?_⟩⟩
  filter_upwards [hsources,Filter.eventually_all.mpr (fun T=>(kc T).2.down.2),
    eventual_geometry_small_frequency g.μ g.μ_pos] with Z hc hk hfreq
  refine ⟨(hk ∅).1,?_⟩
  intro T
  apply affine_main_low_spec_of_receipts (α:=T) M H hH W hW.continuous hWs hbeta g
    ηseed Cs (ks T).2.1 (ks T).1 (kc T).1 η₀ Q hQM hQ72 Z hfreq.2
  · unfold GeometryAffineMainLowSourceSpec
    intro θ η₀' w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots inp
    exact geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
      (hc.2 T η₀' θ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots)
  · exact (hk T).2

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_main_low_profile_zero
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_main_low_target_lower

#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_main_low_spec_of_receipts

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_main_low_payment
