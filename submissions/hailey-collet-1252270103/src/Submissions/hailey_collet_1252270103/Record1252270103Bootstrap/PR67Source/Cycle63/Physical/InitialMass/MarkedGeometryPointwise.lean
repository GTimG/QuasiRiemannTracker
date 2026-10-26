import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedGeometryPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedGeometrySupply
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedParameters
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.MarkedBins
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open Cycle63MarkedPlain Cycle63CommonSupply CenteredMomentCommonProfile
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The literal small-allocation coordinates are in the uniform raw-count
window. The upper gate is inherited from the upward frequency bin. -/
theorem actual_geometry_small_allocation_frequency
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (A a reserve ε εv b width Q : ℝ)(hZ : 1<Z)
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (ha : a≤Cycle63.Arithmetic.amp b)
    (hω : frequencyLoss Z 32 ξ+reserve≤Cycle63.Optimization.frequencyLossCap)(hε : 0≤ε)
    (_hwidth : 0<width)(hQ : Q≤130) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    c+b₂≤Cycle63.Optimization.suppliedAt b → x 2+width≤Q → (4/5:ℝ)≤x 2 ∧ x 2+width≤130 := by
  intro l x c b₂ hsmall hq
  have hh:=actual_geometry_compensated_frequency_gates s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv b hZ (by simpa using ha) (by simpa using hω) hε
  dsimp only at hh
  have hlow : Cycle63.Arithmetic.frequencyAt b-2*(c+b₂)≤x 2 := by
    simpa only [x,c,b₂,l,compensatedHighCoordinates,show (2:Fin 4)≠0 by decide,
      ite_false,mul_one,childHighCoordinates,add_zero] using hh.2.2.2
  have hpos:=allocation_small_frequency (x 2) (c+b₂) b hb hlow hsmall
  exact ⟨by linarith,hq.trans hQ⟩

/-- The actual coordinate ledger retains enough saving to pay the complete
marked count error as well as the old positive high-source reserve. -/
theorem actual_geometry_retained_high_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (A a reserve ε εv b δ live : ℝ)(hZ : 1<Z)
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop)
    (hA : A≤Cycle63.Arithmetic.totalA b)(ha : a≤Cycle63.Arithmetic.amp b)
    (hω : frequencyLoss Z 32 ξ+reserve≤Cycle63.Optimization.frequencyLossCap)(hε : 0≤ε)
    (hlive : 0≤live) (hleft : left=!reflected) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv
    Cycle63.Optimization.suppliedAt b≤ c+b₂+live →
    retainedHighExponent δ (fun q=>Cycle63.Optimization.markedGain δ live ((Cycle63.Optimization.coreFactor)*q)) x≤
      side+target-((Cycle63.Arithmetic.lowReserve)+Cycle63.Optimization.markedLoss) := by
  intro l side x c b₂ target hsupply
  let xc:=compensatedHighCoordinates x side
  have hpay:=actual_geometry_compensated_allocation_payment s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv b δ hZ hb
    ⟨hδ.1,by linarith [hδ.2, Cycle63.Optimization.markedBinTop_bounds.2]⟩ (by norm_num)
    (by simpa using hA) (by simpa using ha) hleft
  have hfreq:=actual_geometry_compensated_frequency_gates s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv b hZ (by simpa using ha) (by simpa using hω) hε
  change highExponentValue δ xc≤target-1*Cycle63.Physical.highMainReserve b δ-
    Cycle63.Optimization.commonRateAt δ*(c+b₂) at hpay
  change 0≤ c ∧ 0≤b₂ ∧ xc 3=A-(c+b₂) ∧ Cycle63.Arithmetic.frequencyAt b*1-2*(c+b₂)≤xc 2 at hfreq
  have hp:=geometry_marked_compensated_payment (E:=highExponentValue δ xc)
    (target:=target) (removed:=c+b₂) (live:=live) (q:=xc 2) (loss:=Cycle63.Optimization.markedLoss)
    hb hδ (by simpa only [one_mul] using hpay)
    (add_nonneg hfreq.1 hfreq.2.1) hlive hsupply (by simpa only [mul_one] using hfreq.2.2.2) le_rfl
  have hident : highExponentValue δ xc=highExponentValue δ x-side :=
    compensated_high_exponent δ side x
  have hx2 : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  rw [hident,hx2] at hp
  unfold retainedHighExponent
  linarith only [hp]

/-- Choosing the actual tiny-slot threshold preserves the original supply
uniformly before both moving common allocations. -/
theorem eventual_geometry_marked_slot_supply (N : ℕ) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(s : Input α),Fintype.card α≤N → a≤ s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : α→ℝ,(∀j,s.P j=Z^(w j)) → (∀j,0≤w j) →
    ∀e : ℝ,e≤∑j,w j → (∑j,w j)≤Cycle63.Optimization.slotTop →
    let slots:=originalSlots (fun j : liveIndices B₂.val=>j.val.val)
    let large:=largeSlots slots w (markedTinyWidth N)
    0≤∑j∈large,w j ∧ (∑j∈large,w j)≤Cycle63.Optimization.slotTop ∧
      e-Cycle63.Optimization.supplyLoss≤Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+∑j∈large,w j := by
  exact eventual_geometry_large_slot_supply N a (markedTinyWidth N) ha
    (marked_tiny_width_gates N).1.le (marked_tiny_width_gates N).2

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
