import Candidate.Cycle63.Physical.InitialMass.SecondHighBins
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
local notation "O" => HeckeFamily.O

/-- The actual high-source exponent coordinates: outside scalar, missing
radical, retained frequency cap, and remaining raw volume. -/
def actualHighCoordinates (reflected left second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε : ℝ) : Fin 4→ℝ :=
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
  let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
  let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
  let g₂ := Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))
  let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
  let ω := frequencyLoss Z 32 ξ+reserve
  ![-a+(2*A-c-d+R+E-M+max (d-c) 0+6*a+ω-(A-c))+(g₂-t₂-b₂),
    Real.logb Z ((firstSourceMissing left l).absNorm:ℝ),
    M-R-max (c-d) 0+Lc-6*a-ω+ε,A-c-b₂]

/-- Exact high scalar payment in the coordinates used for joint binning. -/
theorem actual_high_coordinate_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S-M*((Cycle63.Arithmetic.lowReserve-(Cycle63.Arithmetic.markedPrice*Cycle63.Optimization.suppliedAt b-Cycle63.Optimization.markedLoss)))+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_scalar_payment reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
  dsimp only at hh ⊢
  rw [actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ] at hh
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz] at hh
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hh
  convert he using 1 <;> dsimp [highExponentValue,actualHighCoordinates] <;> ring

/-- Upward bin rounding keeps the strict high reserve, with an explicit loss. -/
theorem actual_high_rounded_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) (width : ℝ) (hw : 0<width) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (exponentBinUpper width (exponentBin width
      (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)))≤
      S-M*((Cycle63.Arithmetic.lowReserve-(Cycle63.Arithmetic.markedPrice*Cycle63.Optimization.suppliedAt b-Cycle63.Optimization.markedLoss)))+(1-ρ)*ω+ρ*ε+4*width := by
  have hh := actual_high_coordinate_payment reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
  have hbnd := high_exponent_bin_payment width δ hw hδ
    (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)
  dsimp only at hh ⊢
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_high_coordinate_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_high_rounded_payment
