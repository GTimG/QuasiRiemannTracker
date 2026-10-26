import Candidate.Cycle63.Physical.InitialMass.MarkedGeometrySupply
import Candidate.Uneven.MainParameters
import Candidate.Uneven.FineSchedule
import Candidate.Uneven.MainPointwise
import Candidate.Target830.High.BalancedMass
import Candidate.Cycle63.Physical.InitialMass.SecondHighBox

/- Original module: Candidate.Uneven.MainHighWidthSupply. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainHigh
open SaturatedPlain
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open Cycle63CommonSupply Cycle63MarkedPlain CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two common allocations and the tiny-slot discard consume at most
the explicit two-trillionth absolute width allowance. The literal
selected width is retained uniformly, before any cell is selected. -/
theorem eventual_geometry_large_slot_supply_actual (N : ℕ) (a wmin : ℝ)
    (ha : 0<a)(hmin : 0 ≤ wmin)(hsmall : (N:ℝ)*wmin ≤ 1/1000000000000) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι),Fintype.card ι ≤ N → a ≤ s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : ι→ℝ,(∀j,s.P j=Z^(w j)) → (∀j,0 ≤ w j) →
    1/50 ≤ ∑j,w j → (∑j,w j) ≤ 1/25 →
    let slots:=originalSlots (fun j : liveIndices B₂.val=>j.val.val)
    let large:=largeSlots slots w wmin
    0 ≤ ∑j∈large,w j ∧ (∑j∈large,w j) ≤ 1/25 ∧
      (∑j,w j)-2/1000000000000 ≤ Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+∑j∈large,w j := by
  filter_upwards [eventual_two_stage_supplied_width (ι:=ι) N a (1/1000000000000) ha (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hscale hw hsupply hupper slots large
  have hcommon:=hZ.2 s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hscale
  have hid : (∑j : liveIndices B₂.val,w j.val.val)=∑j∈slots,w j :=
    double_subtype_sum (liveIndices B₁.val) (liveIndices B₂.val) w
  rw [hid] at hcommon
  have hlarge:=large_width_lower slots w wmin N ((Finset.card_le_univ _).trans hcard) hmin
  refine ⟨Finset.sum_nonneg (fun j _=>hw j),?_,?_⟩
  · exact (Finset.sum_le_univ_sum_of_nonneg hw).trans hupper
  · change (∑j∈slots,w j)-(N:ℝ)*wmin ≤ ∑j∈large,w j at hlarge
    linarith only [hcommon,hlarge,hsmall]

end
end OAI.SevenEighths.MainHigh
end

/- Original module: Candidate.Uneven.MainHighAdmission. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace OAI.SevenEighths.MainHigh
open TargetHigh830 SaturatedPlain
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
     (P : Sil.Uneven.MainSource.Plane)
     (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b width Q : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.MainSource.widthLo Sil.Uneven.MainSource.widthHi) (ha : a ≤ Sil.Uneven.MainSource.amp P b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ Sil.Uneven.MainSource.frequencyAllowance) (herr : 0 ≤ err)
    (hQ : Q ≤ 130) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    c+b2 ≤ Sil.Uneven.MainSource.supplied b → x 2+width ≤ Q → (4/5:ℝ) ≤ x 2 ∧ x 2+width ≤ 130 := by
  intro l x c b2 hsmall hq
  have hh:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (Sil.Uneven.MainSource.amp P b) Sil.Uneven.MainSource.frequencyAllowance 1 hZ
    (by simpa using ha) (by simpa using homega) herr (by norm_num) (by norm_num)
  simp only [one_mul] at hh
  have hl : 1-6*Sil.Uneven.MainSource.amp P b-Sil.Uneven.MainSource.frequencyAllowance-2*(c+b2) ≤ x 2 := by
    simpa only [x,c,b2,l,compensatedHighCoordinates,childHighCoordinates,show (2:Fin 4)≠0 by decide,
      ite_false,add_zero] using hh.2.2.2
  obtain ⟨_,_,_,haamp,_,_,_,_,hsup,_,_⟩:=Sil.Uneven.MainSource.scheduling_guards P hb
  refine ⟨?_,hq.trans hQ⟩
  norm_num [Sil.Uneven.MainSource.frequencyAllowance] at hl
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
    1/50 ≤ ∑j,w j → (∑j,w j) ≤ 1/25 →
    let slots:=Cycle63CommonSupply.originalSlots (fun j : liveIndices B2.val=>j.val.val)
    let large:=largeSlots slots w (fineRawTiny N)
    0 ≤ ∑j∈large,w j ∧ (∑j∈large,w j) ≤ 1/25 ∧
      (∑j,w j)-Sil.Uneven.MainSource.discard ≤ Real.logb Z (C1.absNorm:ℝ)+Real.logb Z (C2.absNorm:ℝ)+∑j∈large,w j := by
  have hid : (2/1000000000000:ℝ)=Sil.Uneven.MainSource.discard := by norm_num [Sil.Uneven.MainSource.discard]
  simpa only [hid] using eventual_geometry_large_slot_supply_actual (ι:=alpha) N a (fineRawTiny N)
    ha (fine_raw_tiny_gates N).1.le ((fine_raw_tiny_gates N).2.trans (by norm_num))

end OAI.SevenEighths.MainHigh
end
