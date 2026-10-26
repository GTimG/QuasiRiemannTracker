/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineParentBranches

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentAllocatedRayDictionary Cycle63InitialMass
local instance affineParentBranchesSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost

variable {α : Type} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
local instance regionalLowSelectedFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable [Cycle63.AffineLedger] in
/-- The local physical LOW-source return interface at one fixed current
parent. All actual source rows, canonical selectors, reciprocal shell
normalizations and inner height denominators are the native ones. EL is
uniform over the whole source configurations of this parent; constructing
its actual attaining depth family is a separate source obligation. -/
def RegionalLowSelectedAt
    (W : ℝ→ℂ)(hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Mcap Lslot Cs : ℝ)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z 28 2 → O → ℝ → Prop)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})(Z EL : ℝ)
    (hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Rc Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRc : Rc ≤ 20)(hRcap : (R.absNorm:ℝ) ≤ Z^Rc)(hMrow : 0 ≤ Mrow)(hMrow1 : Mrow ≤ 1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+g.μ/16)
    (hAdm : Adm 1 (frequencyLoss Z 32 (g.μ/64)+g.μ/8) (g.μ/64))
    (height mesh : ℝ)(hw : ∀j,0 ≤ w j)
    (hwL : ∀j,w j ≤ Lslot)
    (hwr : ∀j,w j/31 ≤ 1)(hmesh : 0 ≤ mesh)(hwm : ∀j,w j ≤ mesh)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (hzslot : Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.B) : Prop :=
    ∀ {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s R seed (Z^Mrow) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    ∀(hamp0 : 0 ≤ amp)(hamp : |amp| ≤ 4)(homega : |omega| ≤ 4)
      (htarget : -1 ≤ geometryAffineLowTarget g (Fintype.card α) amp omega mesh)
      (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
      (hfirstproj : ∀l,seed∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val),
    let rows:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8)
      (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s R seed Z Mrow amp
      (g.μ/64) (g.μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      caps.zero₁ caps.zero₂ r.val.2
    ∀(χ₀ : rows→RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    ∃hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∃hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ)) ≤ Z^(28:ℝ),
    ∃hPNc : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ)) ≤ Z^(Rc+8),
    let st:=fun (r : rows)(ray : RayFourExpansion.RayCharacter)=>retainedState Z 28 hZ ((datum r).τ ray)
      (internalQ Q η₀) ((datum r).R*(if second then (datum r).D else (datum r).C)) (hP r) (hPN r)
      (datum r).radius (datum r).C (datum r).D (datum r).inactive
    ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
    left₁=!reflected → u₀≠0 →
    ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀) ≤ g.δ) →
    let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
    (∀r,∀ray,∀(W' : ℝ)(hW' : (st r ray).width ≤ W'),Presented η₀ Z (widenState (st r ray) W' hW') (mult r) Tz) →
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hbeta hβhi
    let firstMass:=fun l=>geometryFirstHighMass reflected s R seed Ψ Mrow Z (g.μ/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    mainLowPhysicalCompleteCost (Fintype.card α) 1 (1/4) second
      (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
      (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical ≤ (Kall*Z^(geometryAffineLowTarget g (Fintype.card α) amp omega mesh+(1-Mrow))+EL)*
        (p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

end
end OAI.SevenEighths.Cycle153RegionalLow
