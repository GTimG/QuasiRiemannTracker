import Candidate.Cycle62.Physical.InitialMass.MarkedGeometryPayment
import Candidate.Cycle62.Physical.InitialMass.MarkedGeometrySupply
import Candidate.Cycle62.Physical.InitialMass.MarkedParameters
import Candidate.Cycle62.Marked.MarkedBins

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization Cycle62Moment Cycle62HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open Cycle62MarkedPlain Cycle62CommonSupply CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The exact canonical amplifier range lies below the frequency cap used
by the marked allocation ledger. -/
theorem marked_amp_le {b a : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (ha : a≤Cycle62.Arithmetic.amp b) :
    a≤1/80 := by
  have hh:=(Cycle62.Arithmetic.amp_bounds hb).2
  linarith

/-- The literal small-allocation coordinates are in the uniform raw-count
window. The upper gate is inherited from the upward frequency bin. -/
theorem actual_geometry_small_allocation_frequency
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (A a reserve ε εv b width Q : ℝ)(hZ : 1<Z)
    (hb : 3401/100000≤b ∧ b≤1/25)
    (ha : a≤Cycle62.Arithmetic.amp b)
    (hω : frequencyLoss Z 32 ξ+reserve≤1/1000)(hε : 0≤ε)
    (hwidth : 0<width)(hQ : Q≤130) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    c+b₂≤33/1000 → x 2+width≤Q → (4/5:ℝ)≤x 2 ∧ x 2+width≤130 := by
  intro l x c b₂ hsmall hq
  have hh:=actual_geometry_compensated_frequency_gates s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv hZ
    (by simpa using marked_amp_le hb ha) (by simpa using hω) hε
  dsimp only at hh
  have hlow : 231/250-2*(c+b₂)≤x 2 := by
    simpa only [x,c,b₂,l,compensatedHighCoordinates,show (2:Fin 4)≠0 by decide,
      ite_false,mul_one,childHighCoordinates,add_zero] using hh.2.2.2
  have hpos:=allocation_small_frequency (x 2) (c+b₂) hlow hsmall
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
    (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤7/10)
    (hA : A≤Cycle62.Arithmetic.totalA b)(ha : a≤Cycle62.Arithmetic.amp b)
    (hω : frequencyLoss Z 32 ξ+reserve≤1/1000)(hε : 0≤ε)
    (hlive : 0≤live) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv
    33/1000≤c+b₂+live →
    retainedHighExponent δ (fun q=>(7/45)*min live ((3/200)*((122/125)*q))) x≤
      side+target-((720486667/30493190000000)+(1/200000)) := by
  intro l side x c b₂ target hsupply
  let xc:=compensatedHighCoordinates x side
  have hpay:=actual_geometry_compensated_allocation_payment s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv b δ hZ hb hδ (by norm_num)
    (by simpa using hA) (by simpa using ha)
  have hfreq:=actual_geometry_compensated_frequency_gates s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv hZ
    (by simpa using marked_amp_le hb ha) (by simpa using hω) hε
  change highExponentValue δ xc≤target-1*Cycle62.Physical.highMainReserve b δ-(c+b₂)/20 at hpay
  change 0≤c ∧ 0≤b₂ ∧ xc 3=A-(c+b₂) ∧ 231*1/250-2*(c+b₂)≤xc 2 at hfreq
  have hp:=geometry_marked_compensated_payment (E:=highExponentValue δ xc)
    (target:=target) (removed:=c+b₂) (live:=live) (q:=xc 2) (loss:=1/200000)
    hb ⟨hδ.1,by linarith [hδ.2]⟩ (by simpa using hpay)
    (add_nonneg hfreq.1 hfreq.2.1) hlive hsupply (by simpa using hfreq.2.2.2) (by norm_num)
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
    ∀(s : Input α),Fintype.card α≤N → a≤s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : α→ℝ,(∀j,s.P j=Z^(w j)) → (∀j,0≤w j) →
    17/500≤∑j,w j → (∑j,w j)≤1/25 →
    let slots:=originalSlots (fun j : liveIndices B₂.val=>j.val.val)
    let large:=largeSlots slots w (markedTinyWidth N)
    0≤∑j∈large,w j ∧ (∑j∈large,w j)≤1/25 ∧
      33/1000≤Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+∑j∈large,w j := by
  exact eventual_geometry_large_slot_supply N a (markedTinyWidth N) ha
    (marked_tiny_width_gates N).1.le (marked_tiny_width_gates N).2

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_small_allocation_frequency
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_retained_high_payment
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_geometry_marked_slot_supply
