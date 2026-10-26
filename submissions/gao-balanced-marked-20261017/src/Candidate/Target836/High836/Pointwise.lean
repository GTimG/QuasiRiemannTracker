import Candidate.Target836.SourceProvider.HighCoordinates
import Candidate.Target836.SourceProvider.WidthSupply
import Candidate.Target836.Marked836.MarkedRate
import Candidate.Cycle63.Physical.InitialMass.MarkedGeometryPayment
import Candidate.Cycle63.Physical.InitialMass.MarkedGeometrySupply
import Candidate.Cycle63.Physical.InitialMass.MarkedParameters
import Candidate.Cycle63.Marked.MarkedBins

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.TargetHigh836
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
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
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open Cycle63MarkedPlain Cycle63CommonSupply CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The exact canonical amplifier range lies below the frequency cap used
by the marked allocation ledger. -/
theorem marked_amp_le {b a : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (ha : a ≤ Named.amp b) :
    a ≤ 1/75 := by
  exact ha.trans (Named.basic_bounds b hb).2.1

/-- The literal small-allocation coordinates are in the uniform raw-count
window. The upper gate is inherited from the upward frequency bin. -/
theorem actual_geometry_small_allocation_frequency
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (A a reserve ε εv b width Q : ℝ)(hZ : 1<Z)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25)
    (ha : a ≤ Named.amp b)
    (hω : frequencyLoss Z 32 ξ+reserve ≤ 1/1000)(hε : 0 ≤ ε)
    (hwidth : 0<width)(hQ : Q ≤ 130) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    c+b₂ ≤ Named.supplied b → x 2+width ≤ Q → (4/5:ℝ) ≤ x 2 ∧ x 2+width ≤ 130 := by
  intro l x c b₂ hsmall hq
  have hh:=actual_geometry_compensated_frequency_gates s R seed K Z ξ hK bin j d₂
    reflected left second U 1 A a reserve ε εv hZ
    (by simpa using marked_amp_le hb ha) (by simpa using hω) hε
  dsimp only at hh
  have hlow : 919/1000-2*(c+b₂) ≤ x 2 := by
    simpa only [x,c,b₂,l,compensatedHighCoordinates,show (2:Fin 4)≠0 by decide,
      ite_false,mul_one,childHighCoordinates,add_zero] using hh.2.2.2
  have hs := (Named.basic_bounds b hb).2.2.2.1
  exact ⟨by linarith, hq.trans hQ⟩

/-- Choosing the actual tiny-slot threshold preserves the original supply
uniformly before both moving common allocations. -/
theorem eventual_geometry_marked_slot_supply (N : ℕ) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(s : Input α),Fintype.card α ≤ N → a ≤  s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : α→ℝ,(∀j,s.P j=Z^(w j)) → (∀j,0 ≤ w j) →
    17/500 ≤ ∑j,w j → (∑j,w j) ≤ 1/25 →
    let slots:=originalSlots (fun j : liveIndices B₂.val=>j.val.val)
    let large:=largeSlots slots w (markedTinyWidth N)
    0 ≤ ∑j∈large,w j ∧ (∑j∈large,w j) ≤ 1/25 ∧
      (∑j,w j)-1/1000 ≤ Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+∑j∈large,w j := by
  exact Target874836.SourceProvider.eventual_geometry_large_slot_supply_actual N a (markedTinyWidth N) ha
    (marked_tiny_width_gates N).1.le (marked_tiny_width_gates N).2


theorem named_rate_eq_coefficient (δ : ℝ) :
    Named.rate δ = Marked836.VariableSupply.coefficient δ := by
  unfold Named.rate Marked836.VariableSupply.coefficient Marked836.VariableSupply.phi
  ring

/-- The same actual canonical coordinates pay the exact source-bin coefficient.
Both the frequency and surviving-slot supply retain their moving allocation. -/
theorem actual_geometry_retained_high_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (A a reserve ε εv b δ live : ℝ)(hZ : 1<Z)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25)
    (hδ : Named.q ≤ δ ∧ δ ≤ 7/10)
    (hA : A ≤ Named.total b)(ha : a ≤ Named.amp b)
    (hω : frequencyLoss Z 32 ξ+reserve ≤ 1/1000)(hε : 0 ≤ ε)
    (hlive : 0 ≤ live) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv
    Named.supplied b ≤ c+b₂+live →
    retainedHighExponent δ (fun q=>Marked836.VariableSupply.coefficient δ*min live ((13/400)*((122/125)*q))) x ≤ 
      side+target-(Named.highReserve+(1/200000)) := by
  intro l side x c b₂ target hsupply
  let xc:=compensatedHighCoordinates x side
  have hpay:=Target874836.SourceProvider.actual_geometry_compensated_valuation_payment
    s R seed K Z ξ hK bin j d₂ reflected left second U 1 A a reserve ε εv b δ hZ hb
    ⟨hδ.1,by linarith [hδ.2]⟩ (by norm_num) (by simpa using hA) (by simpa using ha)
  have hfreq:=Target874836.SourceProvider.actual_geometry_compensated_moving_frequency
    s R seed K Z ξ hK bin j d₂ reflected left second U 1 A a reserve ε εv b hZ
    (by simpa using ha) (by simpa using hω) hε
  change highExponentValue δ xc ≤ target-1*Named.high b δ-Named.gamma δ*(c+b₂) at hpay
  change 0 ≤ c ∧ 0 ≤ b₂ ∧ xc 3=A-(c+b₂) ∧
    1*Named.frequency b-2*(c+b₂) ≤ Named.core*xc 2 at hfreq
  have hp:=Named.geometry_marked_payment b δ (highExponentValue δ xc) target
    (c+b₂) live (Named.core*xc 2) (1/200000) hb hδ (by simpa using hpay)
    (add_nonneg hfreq.1 hfreq.2.1) hlive hsupply (by simpa using hfreq.2.2.2)
    (by norm_num [Named.loss])
  have hident : highExponentValue δ xc=highExponentValue δ x-side :=
    compensated_high_exponent δ side x
  have hx2 : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  rw [hident,hx2,named_rate_eq_coefficient] at hp
  unfold Named.tau Named.core at hp
  unfold retainedHighExponent
  linarith only [hp]


/-- The unmarked half uses either the upper zero range or the actual removed
width at this source cell. The allocation threshold is not frozen at .033. -/
theorem actual_geometry_unmarked_high_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (A a reserve ε εv b δ : ℝ)(hZ : 1<Z)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4)
    (hA : A ≤ Named.total b)(ha : a ≤ Named.amp b) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z 1 A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv
    (7/10 ≤ δ ∨ Named.supplied b ≤ c+b₂) →
    highExponentValue δ x ≤ side+target-Named.highReserve := by
  intro l side x c b₂ target hbranch
  let xc:=compensatedHighCoordinates x side
  have hpay:=Target874836.SourceProvider.actual_geometry_compensated_valuation_payment
    s R seed K Z ξ hK bin j d₂ reflected left second U 1 A a reserve ε εv b δ hZ hb hδ
    (by norm_num) (by simpa using hA) (by simpa using ha)
  change highExponentValue δ xc ≤ target-1*Named.high b δ-Named.gamma δ*(c+b₂) at hpay
  have hc : 0 ≤ c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 (geometryFirstSource s R seed K Z ξ hK bin j.1).hC.1
    · exact norm_ge_one l.1.2 (geometryFirstSource s R seed K Z ξ hK bin j.1).hD.1
  have hb₂ : 0 ≤ b₂ := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d₂.C d₂.hC.1
    · exact norm_ge_one d₂.D d₂.hD.1
  have hgamma := (Named.gamma_bounds_full hδ).1
  have hreserve : Named.highReserve ≤ Named.high b δ+Named.gamma δ*(c+b₂) := by
    rcases hbranch with hu | hr
    · have hh := Named.high_upper b δ hb ⟨hu,hδ.2⟩
      linarith [mul_nonneg hgamma (add_nonneg hc hb₂)]
    · by_cases hu : 7/10 ≤ δ
      · have hh := Named.high_upper b δ hb ⟨hu,hδ.2⟩
        linarith [mul_nonneg hgamma (add_nonneg hc hb₂)]
      · have hh := (Named.channel_reserves b δ hb ⟨hδ.1,le_of_not_ge hu⟩).1
        have hm := mul_le_mul_of_nonneg_left hr hgamma
        have hl : 0 ≤ Named.loss := by norm_num [Named.loss]
        linarith only [hh, hm, hl]
  have hident : highExponentValue δ xc=highExponentValue δ x-side :=
    compensated_high_exponent δ side x
  rw [hident] at hpay
  linarith only [hpay, hreserve]

end
end OAI.SevenEighths.TargetHigh836
#print axioms OAI.SevenEighths.TargetHigh836.actual_geometry_small_allocation_frequency
#print axioms OAI.SevenEighths.TargetHigh836.eventual_geometry_marked_slot_supply

#print axioms OAI.SevenEighths.TargetHigh836.actual_geometry_retained_high_payment

#print axioms OAI.SevenEighths.TargetHigh836.actual_geometry_unmarked_high_payment
