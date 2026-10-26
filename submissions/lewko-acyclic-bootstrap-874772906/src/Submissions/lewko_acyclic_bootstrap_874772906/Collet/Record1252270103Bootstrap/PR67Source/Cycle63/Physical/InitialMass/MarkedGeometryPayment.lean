import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedHighCoordinates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.MarkedAllocationReserve
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
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The compensated HIGH coordinates of a selected first column pay the parent's reserve
`D (1 - ρ) - δ A - a (5 - 6ρ)` and the cone rate of the bin on both removed widths. -/
theorem actual_geometry_compensated_allocation_payment_reserve
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv δ : ℝ)(hZ : 1 < Z)
    (hδ : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ 3/4)
    (hleft : left=!reflected) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
        (D*(1-unmarkedDensity δ)-δ*A-a*(5-6*unmarkedDensity δ))-ValuationCone.commonRate δ*(c+b₂) := by
  intro l side x c b₂
  subst hleft
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD' : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z ξ hK bin j.1).sameSupport
  have hh:=actual_high_coordinate_allocation_payment_reserve reflected second l hC hD' heq
    d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z δ D A a ξ reserve ε hZ hδ
  have he:=actual_geometry_high_side_identity s R seed K Z ξ hK bin j reflected A
  change side=_ at he
  have hs:=actual_geometry_surplus_eq s R seed K Z ξ hK bin j reflected
  dsimp only at hh hs
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  dsimp only [c,b₂]
  linarith only [hh,he,hs]

/-- The compensated HIGH coordinates of a selected first column pay the HIGH reserve of the cell and the cone rate of
the bin on both removed widths. -/
theorem actual_geometry_compensated_allocation_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b δ : ℝ)(hZ : 1<Z)
    (_hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)(_hD : 0≤D)
    (hA : A≤D*Cycle63.Arithmetic.totalA b)(ha : a≤D*Cycle63.Arithmetic.amp b)
    (hleft : left=!reflected) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
        D*Cycle63.Physical.highMainReserve b δ-ValuationCone.commonRate δ*(c+b₂) := by
  have hh := actual_geometry_compensated_allocation_payment_reserve s R seed K Z ξ hK bin j d₂ reflected left
    second U D A a reserve ε εv δ hZ hδ hleft
  have hr := Cycle63.Physical.highMainReserve_le_reserve hδ hA ha
  dsimp only at hh ⊢
  linarith only [hh, hr]

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
    (hleft : left=!reflected) (hreserve : μ≤Cycle63.Physical.highMainReserve b δ) :
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
    (ha : a≤D*Cycle63.Arithmetic.amp b)(hω : frequencyLoss Z 32 ξ+reserve≤D*Cycle63.Optimization.frequencyLossCap)
    (hε : 0≤ε) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    0≤ c ∧ 0≤b₂ ∧ x 3=A-(c+b₂) ∧ Cycle63.Arithmetic.frequencyAt b*D-2*(c+b₂)≤x 2 := by
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
  · apply MarkedAllocationReserve.raw_frequency_lower b D c
      (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) b₂ a
      (Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ))
      (Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ))
      (frequencyLoss Z 32 ξ+reserve) ε (x 2) hc hd hb₂ hR hLc ha hω hε
    simp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c]

/-- The remaining branch has a uniformly positive raw frequency window. -/
theorem allocation_small_frequency (q removed b : ℝ)
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hq : Cycle63.Arithmetic.frequencyAt b-2*removed≤q)
    (hsmall : removed≤Cycle63.Optimization.suppliedAt b) : 4/5≤q := by
  have hf := Cycle63.Arithmetic.frequencyAt_lower hb
  linarith

/-- The actual retained width pays the negative raw reserve, after all analytic losses: the HIGH
reserve, the removed width at the common rate and the exact marked gain of the live width keep the
room `lowReserve` and the loss. -/
theorem geometry_marked_compensated_payment {b δ E target removed live q loss : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop)
    (hE : E≤target-Cycle63.Physical.highMainReserve b δ-Cycle63.Optimization.commonRateAt δ*removed)
    (hu : 0≤ removed)(hlive : 0≤live)(hsupply : Cycle63.Optimization.suppliedAt b≤ removed+live)
    (hq : Cycle63.Arithmetic.frequencyAt b-2*removed≤q)(hloss : loss≤Cycle63.Optimization.markedLoss) :
    E-Cycle63.Optimization.markedGain δ live ((Cycle63.Optimization.coreFactor)*q)+loss≤
      target-Cycle63.Arithmetic.lowReserve := by
  have h := MarkedAllocationReserve.marked_allocation_payment hb hδ hu hlive hsupply hq
  linarith only [h, hE, hloss]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
