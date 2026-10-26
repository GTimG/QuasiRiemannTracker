import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.AffineProfileZero
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePhysicalSelection
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLowChildrenPresented
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

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

variable [Cycle63.AffineLedger] in
/-- Only positive fees accompany the single negative low reserve. -/
theorem affine_main_low_target_lower (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ)(ha : 0≤amp)(ho : 0≤omega)(hm : 0≤ mesh) :
    -1≤geometryAffineLowTarget g N amp omega mesh := by
  have hq : 0≤Cycle63.AffineLedger.q := Cycle63.AffineLedger.q_pos.le
  have hmu:=g.μ_pos.le
  have hd:=g.δ_pos.le
  unfold geometryAffineLowTarget
  have hp : 0≤Cycle63.AffineLedger.lowRate*(omega+g.μ/8) :=
    mul_nonneg Cycle63.AffineLedger.lowRate_mem.1.le (by positivity)
  have hpm : 0≤Cycle63.AffineLedger.q*mesh := mul_nonneg hq hm
  have hN : 0≤2*g.δ*31*(N:ℝ) := by positivity
  have hs : 0≤3*((N:ℝ)+2)*3*g.δ := by positivity
  have hlow : Cycle63.AffineLedger.lowReserve ≤ 1 := Cycle63.AffineLedger.lowReserve_le.trans (by norm_num)
  linarith

set_option linter.unusedVariables false in
set_option linter.defProp false in
set_option maxHeartbeats 160000 in
def GeometryAffineMainLowSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(Mcap Lslot : ℝ)
    (ηseed : Character)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤Lslot)(hwm : ∀i,w i≤ mesh)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)),
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_profile_zero p 1
    ∀{Label : Type}[Fintype Label]
      (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
      (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
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
    (∀i,0≤w i) → Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z

attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost
set_option maxHeartbeats 180000 in
theorem affine_main_low_spec_of_receipts {Adm : ℝ→ℝ→ℝ→Prop}
    {Presented : Character → (Z : ℝ) → NaturalState Z 28 2 → O → ℝ → Prop}
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(Mcap Lslot : ℝ)
    (ηseed : Character)(Cs : ℝ)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ)
    (hω : 0≤frequencyLoss Z 32 (g.μ/64)+g.μ/8 ∧
      frequencyLoss Z 32 (g.μ/64)+g.μ/8≤33*g.μ/128)
    (hanchor : Real.logb Z (ηseed.modulus.absNorm:ℝ)≤g.μ/16)
    (hcaps : GeometryAffineMainLowSourceSpec (α:=α) M H hH W hW hWs Cs Z)
    (hAdm : Adm 1 (frequencyLoss Z 32 (g.μ/64)+g.μ/8) (g.μ/64))
    (u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)(τT : ℝ)
    (hu₀norm : Real.logb Z (normValue u₀)≤g.δ)(hpar : ParentPresentation ηseed F₀ R₀)
    (hpres : GeometryLowChildrenPresented (α:=α) Presented τT η₀ u₀ F₀ R₀ 8)
    (hspec : GeometryAffineLowSelectedSpec (α:=α) M H hH W hbeta g Mcap Lslot Cs Adm Presented Sp degreeAll Kall η₀ Q hQM
      hQ72 Z) :
    GeometryAffineMainLowSpec (α:=α) M H hH W hW hWs hbeta g Mcap Lslot ηseed Sp degreeAll Kall η₀ Q hQM hQ72 Z := by
  unfold GeometryAffineMainLowSpec
  intro hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh hw hmesh hmeshcap hwm
    hheight hfreq hT hβhi hwin s hz₁ hz₂
    Label _ reflected second bin t firstIndex first amp omega hf₁ hinj rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u
  have cap₀:=hcaps θ η₀ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hwin
  obtain ⟨caps,hm⟩:=actual_affine_low_source_gates M H hH η₀ θ W hW hWs w σ freq hσ state p
    tplain X₁ X₂ hX₁ hX₂ Cs hZ hw hwin cap₀
  have hlogs : ∀j,Real.logb Z (s.P j)=w j := by
    intro j
    change Real.logb Z (Z^(w j))=w j
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hsum : (∑j,Real.logb Z (s.P j))=∑j,w j := Finset.sum_congr rfl (fun j _=>hlogs j)
  have hηs : s.η=ηseed := hη
  have hw₁ (j : α) : w j≤1 :=
    (Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)).trans (hwin.slots_le.trans Cycle63.AffineLedger.slotTop_le_one)
  have hwr (j : α) : w j/31≤1 := by linarith [hw₁ j]
  have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨hwin.slots_ge,hwin.slots_le⟩
  have hbetaCell:=Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := by
    simpa only [amp,hsum,div_one,one_mul] using (Cycle63.AffineLedger.amp_pos hbetaCell).le
  have hamp : |amp|≤4 := by
    rw [abs_of_nonneg hamp0]
    have h:= (Cycle63.AffineLedger.amp_bounds hbetaCell).2.trans (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one] :
      Cycle63.AffineLedger.amplifierCap≤4)
    simpa only [amp,hsum,div_one,one_mul] using h
  have homega : |omega|≤4 := by
    rw [abs_of_nonneg hω.1]
    exact hω.2.trans (by linarith [g.μ_cap])
  have htarget:=affine_main_low_target_lower g (Fintype.card α) amp omega mesh hamp0 hω.1 hmesh
  unfold GeometryAffineLowSelectedSpec at hspec
  have hone : ((1:Ideal O).absNorm:ℝ)≤Z^(0:ℝ) := by
    rw [Ideal.one_eq_top,Ideal.absNorm_top,Nat.cast_one,Real.rpow_zero]
  have hb:=hspec (Label:=Label) hZ s p caps θ w σ freq hm 1 1 0 1 one_ne_zero squarefree_one (by norm_num) hone zero_le_one le_rfl
    (by rw [hηs]; linarith only [hanchor]) hAdm height mesh hw
    (fun j=>(hwm j).trans hmeshcap) hwr hmesh hwm hσ hheight hfreq hT hβhi
    (by rw [hsum]; exact ⟨hwin.slots_ge,hwin.slots_le⟩) (by
      change length Z X₁+length Z X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B
      rw [hsum]; exact hwin.plane)
    reflected second bin t firstIndex hamp0 hamp homega htarget hf₁ hinj (fun l=>one_dvd _) χ₀ m hm₀ hml hm₂ Ψ t₀ u
  obtain ⟨hP,hPN,hPNc,hcost⟩:=hb
  have hPNc8 : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(8:ℝ) :=
    fun r=>by simpa only [zero_add] using hPNc r
  refine ⟨hP,hPN,?_⟩
  obtain ⟨B₂,rwitness,hgood⟩:=actual_main_low_family_choices reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4) t
    (Fintype.card α) hZ bin hz₁ hz₂
    (mainLowSelectedOriginal reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4) t (Fintype.card α) hZ bin hz₁ hz₂
      firstIndex) second
  have hparent : ParentPresentation s.η F₀ R₀ := by rw [hηs]; exact hpar
  simpa only [sub_self,add_zero] using
    hcost (!reflected) u₀ (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l : O)) (Z^τT) rfl hu₀
      ⟨fun l=>Units.isUnit _,hu₀norm⟩
      (fun r ray W' hW'=>hpres hu₀ reflected second s hparent 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4) t
        (Fintype.card α) hZ bin (firstIndex r.val.1) hz₁ hz₂ r.val.2 (B₂ r) (rwitness r) (hf₁ r.val.1)
        (hgood r).1 ray Q (hP r) (hPN r) (hPNc8 r) W' hW')

attribute [local irreducible] GeometryAffineMainLowSpec GeometryAffineLowSelectedSpec
attribute [local irreducible] actual_affine_low_selected_payment
set_option maxHeartbeats 180000 in
def actual_affine_main_low_payment {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(Mcap Lslot : ℝ)
    (hMcap1 : 101/100≤Mcap)(hMcap2 : Mcap≤2)(hrow5 : LowSelectedPaidAt M H hH g Mcap Lslot Adm labelExp Presented)
    (ηseed : Character)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (hAdm : ∀ᶠZ : ℝ in atTop,Adm 1 (frequencyLoss Z 32 (g.μ/64)+g.μ/8) (g.μ/64))
    (τT : ℝ)(hpar : ParentPresentation ηseed F₀ R₀)
    (hpres : ∀T : Finset α,GeometryLowChildrenPresented (α:=T) (Presented 28) τT ηcoarse u₀ F₀ R₀ 8) :
    ΣCs : ℝ,PLift (1≤Cs) ×
      ∀(Q : Ideal O)(hQM : Q≤M),
        internalQ Q ηcoarse≠0 → internalQ Q ηcoarse≠⊤ → ∀hQ72 : internalQ Q ηcoarse≤Ideal.span {(72:O)},
        ΣdegreeAll : Finset α→ℕ,ΣSp : Finset α→Finset (ℕ×ℕ),PLift (∀T,(0,0)∈Sp T) ×
          ΣKall : Finset α→ℝ,PLift ((∀T,0<Kall T) ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
            ∀T : Finset α,GeometryAffineMainLowSpec (α:=T) M H hH W hW.continuous hWs hbeta g Mcap Lslot
              ηseed (Sp T) (degreeAll T) (Kall T) ηcoarse Q hQM hQ72 Z) := by
  let sources:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW.continuous hWs
  let Cs:=Classical.choose sources
  have hCs:=(Classical.choose_spec sources).1
  have hsources:=(Classical.choose_spec sources).2
  refine ⟨Cs,PLift.up hCs,?_⟩
  intro Q hQM hQ0 hQt hQ72
  let kc (T : Finset α):=actual_affine_low_selected_payment (α:=T) M H hH hgate W hWs hW hbeta g Mcap Lslot
    hMcap1 hMcap2 hrow5 Cs hCs ηcoarse u₀ F₀ R₀ hu₀ ηcoarse Q hQM hQ0 hQt hQ72
  refine ⟨(fun T=>(kc T).1),(fun T=>(kc T).2.1),PLift.up (fun T=>(kc T).2.2.1.down),
    (fun T=>(kc T).2.2.2.1),PLift.up ⟨(fun T=>(kc T).2.2.2.2.down.1),?_⟩⟩
  have hnorm : ∀ᶠZ : ℝ in atTop,Real.logb Z (normValue u₀)≤g.δ := by
    filter_upwards [(tendsto_rpow_atTop g.δ_pos).eventually (eventually_ge_atTop (normValue u₀)),
      eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
    exact (Real.logb_le_iff_le_rpow hZ1 (normValue_pos u₀ hu₀)).mpr hZ
  filter_upwards [hsources,Filter.eventually_all.mpr (fun T=>(kc T).2.2.2.2.down.2),
    eventual_geometry_small_frequency g.μ g.μ_pos,
    Cycle63Moment.fixed_anchor_width_uniform (fun _:Unit=>ηseed) 1 (g.μ/16) one_pos
      (by linarith only [g.μ_pos]),hAdm,hnorm] with Z hc hk hfreq hanchor hAdmZ hnormZ
  refine ⟨(hk ∅).1,?_⟩
  intro T
  refine affine_main_low_spec_of_receipts (α:=T) M H hH W hW.continuous hWs hbeta g Mcap Lslot
    ηseed Cs (kc T).2.1 (kc T).1 (kc T).2.2.2.1 ηcoarse Q hQM hQ72 Z hfreq.2
    (by have h := hanchor.2 () 1 le_rfl; rw [mul_one] at h; exact h) ?_ hAdmZ u₀ F₀ R₀ hu₀ τT hnormZ hpar
    (hpres T) (hk T).2
  unfold GeometryAffineMainLowSourceSpec
  intro θ η₀' w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hwin inp
  exact geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
    (hc.2 T η₀' θ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hwin)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
