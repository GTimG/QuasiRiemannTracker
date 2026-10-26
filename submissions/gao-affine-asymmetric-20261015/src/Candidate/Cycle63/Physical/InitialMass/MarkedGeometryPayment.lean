import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle63.Physical.InitialMass.MarkedHighCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63InitialMass
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
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

theorem actual_geometry_compensated_allocation_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b δ : ℝ)(hZ : 1<Z)
    (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤7/10)(hD : 0≤D)
    (hA : A≤D*Cycle63.Arithmetic.totalA b)(ha : a≤D*Cycle63.Arithmetic.amp b) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
        D*Cycle63.Physical.highMainReserve b δ-(519/4550)*(c+b₂) := by
  intro l side x c b₂
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD' : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z ξ hK bin j.1).sameSupport
  have hh:=actual_high_coordinate_allocation_payment reflected left second l hC hD' heq
    d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z b δ D A a ξ reserve ε hZ hb hδ hD hA ha
  have he:=actual_geometry_high_side_identity s R seed K Z ξ hK bin j reflected A
  change side=_ at he
  dsimp only at hh
  rw [←he] at hh
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  dsimp only [c,b₂]
  linarith only [hh]

theorem actual_geometry_compensated_payment_of_reserve
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b δ μ : ℝ)(hZ : 1<Z)
    (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)(hD : 0≤D)
    (hA : A≤D*Cycle63.Arithmetic.totalA b)(ha : a≤D*Cycle63.Arithmetic.amp b)
    (hreserve : μ≤Cycle63.Physical.highMainReserve b δ) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-D*μ := by
  intro l side x
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD' : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z ξ hK bin j.1).sameSupport
  have hh:=actual_high_coordinate_payment_of_reserve reflected left second l hC hD' heq
    d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z b δ D A a ξ reserve ε μ hZ hb hδ hD hA ha hreserve
  have he:=actual_geometry_high_side_identity s R seed K Z ξ hK bin j reflected A
  change side=_ at he
  dsimp only at hh
  rw [←he] at hh
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  linarith only [hh]


/-- The moving frequency and raw volume retain their literal common-allocation dependence. -/
theorem actual_geometry_compensated_frequency_gates
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv : ℝ)(hZ : 1<Z)
    (ha : a≤D/75)(hω : frequencyLoss Z 32 ξ+reserve≤D/1000)(hε : 0≤ε) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    0≤c ∧ 0≤b₂ ∧ x 3=A-(c+b₂) ∧ 919*D/1000-2*(c+b₂)≤x 2 := by
  intro l side x c b₂
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have hc : 0≤c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 hC.1
    · exact norm_ge_one l.1.2 hD.1
  have hd : 0≤Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.2 hD.1
    · exact norm_ge_one l.1.1 hC.1
  have hb₂ : 0≤b₂ := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d₂.C d₂.hC.1
    · exact norm_ge_one d₂.D d₂.hD.1
  have hg:=actual_first_gates left l hC hD Z hZ
  have hR : Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)≤c := by
    cases reflected
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.1
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.2.1
  have hLc : 0≤Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero left l hC))
  refine ⟨hc,hb₂,?_,?_⟩
  · dsimp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c,b₂]
    ring
  · apply MarkedAllocationReserve.raw_frequency_lower D c
      (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) b₂ a
      (Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ))
      (Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ))
      (frequencyLoss Z 32 ξ+reserve) ε (x 2) hc hd hb₂ hR hLc ha hω hε
    simp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c]

/-- The large-allocation branch pays without any marked estimate. -/
theorem allocation_large_payment (E base removed : ℝ)
    (hE : E≤base-(519/4550)*removed)(hlarge : 33/1000≤removed) :
    E≤base-37/10000 := by linarith

/-- The remaining branch has a uniformly positive raw frequency window. -/
theorem allocation_small_frequency (q removed : ℝ)
    (hq : 919/1000-2*removed≤q)(hsmall : removed≤33/1000) :
    853/1000≤q := by linarith



/-- The actual retained width pays the negative raw reserve, after all
analytic losses. This applies directly to compensated geometric coordinates. -/
theorem geometry_marked_compensated_payment {b δ E target removed live q loss : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)
    (hE : E≤target-Cycle63.Physical.highMainReserve b δ-(519/4550)*removed)
    (hu : 0≤removed)(hlive : 0≤live)(hsupply : 33/1000≤removed+live)
    (hq : 919/1000-2*removed≤q)(hloss : loss≤1/20000) :
    E-(224/1755)*min live ((13/400)*((122/125)*q))+loss≤
      target-720486667/30493190000000 := by
  have hcore : 1121*(1:ℝ)/1250-2*removed≤(122/125)*q :=
    MarkedAllocationReserve.small_core_frequency_lower 1 removed q ((122/125)*q)
      (by norm_num) hu (by simpa using hq) le_rfl
  have hgain:=MarkedAllocationReserve.continuous_marked_ledger 1 removed 0 live ((122/125)*q) δ
    (by norm_num) hu (by norm_num) hlive (by norm_num [Cycle63.Arithmetic.q0] at hδ;linarith [hδ.1])
    (by simpa using hsupply) hcore
  have hreserve:=Cycle63.Physical.marked_high_reserve hb hδ
  simp only [mul_zero,add_zero,zero_add,one_mul,mul_one] at hgain
  have heq : 13*((122/125)*q)/400=(13/400)*((122/125)*q) := by ring
  rw [heq] at hgain
  linarith only [hE,hgain,hloss,hreserve]


end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_compensated_allocation_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_compensated_payment_of_reserve

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_compensated_frequency_gates

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_marked_compensated_payment
