import Candidate.Target830.High.Pointwise
import Candidate.Target830.High.WidthSupply
import Candidate.Target830.High.BalancedMass
import Candidate.Cycle63.Physical.InitialMass.SecondHighBox

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open Target830
open scoped BigOperators
open Cycle63MarkedPlain
open Cycle63CommonSupply
open Marked830Plain CenteredMomentCommonProfile CenteredMomentExceptionalAmplitudePair
open CenteredMomentEnergyState CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem actual_geometry_small_allocation_frequency
    (P : SourcePlane) (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b width Q : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc widthLower widthUpper) (ha : a ≤ P.amp b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ frequencyAllowance) (herr : 0 ≤ err)
    (hQ : Q ≤ 130) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    c+b2 ≤ P.supplied b → x 2+width ≤ Q → (4/5:ℝ) ≤ x 2 ∧ x 2+width ≤ 130 := by
  intro l x c b2 hsmall hq
  have hh:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (P.amp b) frequencyAllowance 1 hZ
    (by simpa using ha) (by simpa using homega) herr (by norm_num) (by norm_num)
  simp only [one_mul] at hh
  have hl : 1-6*P.amp b-frequencyAllowance-2*(c+b2) ≤ x 2 := by
    simpa only [x,c,b2,l,compensatedHighCoordinates,childHighCoordinates,show (2:Fin 4)≠0 by decide,
      ite_false,add_zero] using hh.2.2.2
  obtain ⟨_,_,_,haamp,_,_,_,_,hsup,_,_⟩:=Source.source_guards P hb
  refine ⟨?_,hq.trans hQ⟩
  norm_num [frequencyAllowance] at hl
  linarith

theorem eventual_geometry_marked_slot_supply (N : ℕ) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(s : Input alpha),Fintype.card alpha ≤ N → a ≤ s.lower →
    ∀(C1 R1 : Ideal O)(B1 : actualAllocations s.pools C1),
    frozenCoefficient B1.val C1 R1 s.ν s.W s.P≠0 →
    ∀(chi : Character)(t : ℝ)(C2 R2 : Ideal O)
      (B2 : actualAllocations (child s C1 R1 B1 chi t).pools C2),
    (let first:=child s C1 R1 B1 chi t;
      frozenCoefficient B2.val C2 R2 first.ν first.W first.P≠0) →
    ∀w : alpha→ℝ,(∀j,s.P j=Z^(w j)) → (∀j,0 ≤ w j) →
    17/500 ≤ ∑j,w j → (∑j,w j) ≤ 1/25 →
    let slots:=Cycle63CommonSupply.originalSlots (fun j : liveIndices B2.val=>j.val.val)
    let large:=largeSlots slots w (rawTiny830 N)
    0 ≤ ∑j∈large,w j ∧ (∑j∈large,w j) ≤ 1/25 ∧
      (∑j,w j)-sourceDiscard ≤ Real.logb Z (C1.absNorm:ℝ)+Real.logb Z (C2.absNorm:ℝ)+∑j∈large,w j := by
  have hid : (2/1000000000:ℝ)=sourceDiscard := by norm_num [sourceDiscard]
  simpa only [hid] using eventual_geometry_large_slot_supply_actual (ι:=alpha) N a (rawTiny830 N)
    ha (raw_tiny830_gates N).1.le (raw_tiny830_gates N).2

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_small_allocation_frequency
#print axioms OAI.SevenEighths.TargetHigh830.eventual_geometry_marked_slot_supply
