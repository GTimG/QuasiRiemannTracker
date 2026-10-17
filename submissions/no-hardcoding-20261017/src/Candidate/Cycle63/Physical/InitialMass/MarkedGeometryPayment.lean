import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle63.Physical.InitialMass.MarkedHighCoordinates
import Candidate.Cycle63.Arithmetic.Constants

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
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop)(hD : 0≤D)
    (hA : A≤D*Cycle63.Arithmetic.totalA b)(ha : a≤D*Cycle63.Arithmetic.amp b) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
        D*Cycle63.Physical.highMainReserve b δ-(Cycle63.Arithmetic.markedPrice)*(c+b₂) := by
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
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
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
    (ha : a≤D*Cycle63.Optimization.amplifierCap)(hω : frequencyLoss Z 32 ξ+reserve≤D*Cycle63.Optimization.frequencyLossCap)
    (hε : 0≤ε) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    0≤c ∧ 0≤b₂ ∧ x 3=A-(c+b₂) ∧ Cycle63.Optimization.frequencyFactor*D-2*(c+b₂)≤x 2 := by
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

/-- The remaining branch has a uniformly positive raw frequency window. -/
theorem allocation_small_frequency (q removed b : ℝ) (hb : b≤Cycle63.Optimization.slotTop)
    (hq : Cycle63.Optimization.frequencyFactor-2*removed≤q)(hsmall : removed≤Cycle63.Optimization.suppliedAt b) :
    4/5≤q := by
  have hf := Cycle63.Optimization.frequencyFactor_bounds
  have hl := Cycle63.Optimization.supplyLoss_pos
  unfold Cycle63.Optimization.suppliedAt Cycle63.Optimization.cellMesh at hsmall
  unfold Cycle63.Optimization.slotTop at hb
  linarith [Cycle63.Optimization.allowanceUnit_pos]



/-- The actual retained width pays the negative raw reserve, after all
analytic losses. This applies directly to compensated geometric coordinates; the live width is paid
at the live rate of the bin. -/
theorem geometry_marked_compensated_payment {b δ E target removed live q loss : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)
    (hE : E≤target-Cycle63.Physical.highMainReserve b δ-Cycle63.Arithmetic.markedPrice*removed)
    (hu : 0≤removed)(hlive : 0≤live)(hsupply : Cycle63.Optimization.suppliedAt b≤removed+live)
    (hq : Cycle63.Optimization.frequencyFactor-2*removed≤q)(hloss : loss≤Cycle63.Optimization.markedLoss) :
    E-Cycle63.Optimization.liveRate δ*min live ((Cycle63.Optimization.inverseWidthCap)*((Cycle63.Optimization.coreFactor)*q))+loss≤
      target-Cycle63.Arithmetic.lowReserve := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hcore : Cycle63.Optimization.liveFrequency*1-2*removed≤Cycle63.Optimization.coreFactor*q :=
    MarkedAllocationReserve.small_core_frequency_lower 1 removed q (Cycle63.Optimization.coreFactor*q)
      (by norm_num) hu (by simpa using hq) le_rfl
  have hpδ : Cycle63.Arithmetic.markedPrice≤δ :=
    Cycle63.Arithmetic.markedPrice_le_q0.trans hδ.1
  have hrate0 : 0 ≤ Cycle63.Optimization.liveRate δ := by
    apply le_of_lt
    unfold Cycle63.Optimization.liveRate Cycle63.Optimization.liveRatio
      Cycle63.Optimization.chosenPerUnit Cycle63.Optimization.plainCapacityCost
      Cycle63.Optimization.halfGain
    rat_pos [hq0b, hδ]
  have hcrate := Cycle63.Arithmetic.markedPrice_rate hδ
  have hgain:=MarkedAllocationReserve.continuous_marked_ledger 1 removed 0 live (Cycle63.Optimization.coreFactor*q) δ
    Cycle63.Arithmetic.markedPrice (Cycle63.Optimization.liveRate δ) b hb.1 (by norm_num) hu le_rfl hlive
    hpδ hrate0 hcrate (by simpa using hsupply) hcore
  have hreserve:=Cycle63.Physical.marked_high_reserve_at hb hδ
  have hgross : MarkedAllocationReserve.ledgerMinimum b Cycle63.Arithmetic.markedPrice
      (Cycle63.Optimization.liveRate δ) = Cycle63.Arithmetic.markedGrossAt b δ := by
    rfl
  rw [hgross] at hgain
  simp only [mul_zero,add_zero,zero_add,one_mul,mul_one] at hgain
  linarith only [hE,hgain,hloss,hreserve]

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_compensated_allocation_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_compensated_payment_of_reserve

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_compensated_frequency_gates

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_marked_compensated_payment
