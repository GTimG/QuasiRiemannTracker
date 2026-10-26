import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootDefinitions
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle63.Physical.InitialMass.MarkedHighCoordinates
import Candidate.Cycle63.Arithmetic.Constants
import Candidate.Cycle63.Physical.MarkedAllocationReserve

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
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
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The compensated HIGH coordinates of a selected first column pay the HIGH reserve of the cell and the cone rate of
the bin on both removed widths. -/
theorem actual_geometry_compensated_allocation_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b δ : ℝ)(hZ : 1<Z)
    (_hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle153.MarkedRootPrice.top)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)(_hD : 0≤D)
    (hA : A≤D*Cycle153.MarkedRootPrice.totalA b)(ha : a≤D*Cycle153.MarkedRootPrice.amp b)
    (hleft : left=!reflected) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
        D*Cycle153.MarkedRootPrice.highMainReserve b δ-ValuationCone.commonRate δ*(c+b₂) := by
  have hh := actual_geometry_compensated_allocation_payment_reserve s R seed K Z ξ hK bin j d₂ reflected left
    second U D A a reserve ε εv δ hZ hδ hleft
  have hr := Cycle153.MarkedRootPrice.highMainReserve_le_reserve hδ hA ha
  dsimp only at hh ⊢
  linarith only [hh, hr]

theorem actual_geometry_compensated_payment_of_reserve
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b δ μ : ℝ)(hZ : 1<Z)
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle153.MarkedRootPrice.top)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)(hD : 0≤D)
    (hA : A≤D*Cycle153.MarkedRootPrice.totalA b)(ha : a≤D*Cycle153.MarkedRootPrice.amp b)
    (hleft : left=!reflected) (hreserve : μ≤Cycle153.MarkedRootPrice.highMainReserve b δ) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-D*μ := by
  intro l side x
  have hh := actual_geometry_compensated_allocation_payment s R seed K Z ξ hK bin j d₂ reflected left
    second U D A a reserve ε εv b δ hZ hb hδ hD hA ha hleft
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD' : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have hc : 0≤Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ) :=
    Real.logb_nonneg hZ (by cases reflected <;> exact norm_ge_one _ (by
      first | exact hC.1 | exact hD'.1))
  have hb₂ : 0≤Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ) :=
    Real.logb_nonneg hZ (by cases second <;> exact norm_ge_one _ (by
      first | exact d₂.hC.1 | exact d₂.hD.1))
  have hγ := mul_nonneg (Cycle63.Physical.commonRate_nonneg hδ) (add_nonneg hc hb₂)
  have hμ := mul_le_mul_of_nonneg_left hreserve hD
  dsimp only at hh
  refine hh.trans ?_
  linarith only [hγ, hμ]

/-- The moving frequency and raw volume retain their literal common-allocation dependence. -/
theorem actual_geometry_compensated_frequency_gates
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b : ℝ)(hZ : 1<Z)
    (ha : a≤D*Cycle153.MarkedRootPrice.amp b)(hω : frequencyLoss Z 32 ξ+reserve≤D*Cycle63.Optimization.frequencyLossCap)
    (hε : 0≤ε) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    0≤ c ∧ 0≤b₂ ∧ x 3=A-(c+b₂) ∧ Cycle153.MarkedRootPrice.frequencyAt b*D-2*(c+b₂)≤x 2 := by
  intro l side x c b₂
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have hc : 0≤ c := by
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
  have hR : Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)≤ c := by
    cases reflected
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.1
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.2.1
  have hLc : 0≤Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero left l hC))
  refine ⟨hc,hb₂,?_,?_⟩
  · dsimp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c,b₂]
    ring
  · apply Cycle153.MarkedRootPrice.raw_frequency_lower D c
      (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) b₂ a
      (Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ))
      (Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ))
      (frequencyLoss Z 32 ξ+reserve) ε (x 2) b hc hd hb₂ hR hLc ha hω hε
    simp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c]

/-- The remaining branch has a uniformly positive raw frequency window. -/
theorem allocation_small_frequency (q removed b : ℝ)
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle153.MarkedRootPrice.top)
    (hq : Cycle153.MarkedRootPrice.frequencyAt b-2*removed≤q)
    (hsmall : removed≤Cycle63.Optimization.suppliedAt b) : 4/5≤q := by
  have hf := Cycle153.MarkedRootPrice.frequencyAt_lower hb
  linarith

/-- The actual retained width pays the negative raw reserve, after all analytic losses: the HIGH
reserve, the removed width at the common rate and the exact marked gain of the live width keep the
room `lowReserve` and the loss. -/
theorem geometry_marked_compensated_payment {b δ E target removed live q loss : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle153.MarkedRootPrice.top)
    (hδ : Cycle153.MarkedRootPrice.q≤δ ∧ δ≤(2/3:ℝ))
    (hE : E≤target-Cycle153.MarkedRootPrice.highMainReserve b δ-Cycle63.Optimization.commonRateAt δ*removed)
    (hu : 0≤ removed)(hlive : 0≤live)(hsupply : Cycle63.Optimization.suppliedAt b≤ removed+live)
    (hq : Cycle153.MarkedRootPrice.frequencyAt b-2*removed≤q)(hloss : loss≤Cycle153.MarkedRootPrice.markedLoss) :
    E-Cycle63.Optimization.markedGain δ live ((Cycle63.Optimization.coreFactor)*q)+loss≤
      target-Cycle153.MarkedRootPrice.lowReserve := by
  have h := Cycle153.MarkedRootPrice.marked_allocation_payment hδ hb hu hlive hsupply hq
  change Cycle153.MarkedRootPrice.lowReserve+Cycle153.MarkedRootPrice.markedLoss ≤
    Cycle153.MarkedRootPrice.highMainReserve b δ+Cycle63.Optimization.commonRateAt δ*removed+
      Cycle63.Optimization.markedGain δ live (Cycle63.Optimization.coreFactor*q) at h
  linarith only [h, hE, hloss]

end
end OAI.SevenEighths.Cycle153RootHigh
