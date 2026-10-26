import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildHighSide
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildSideExponent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseSupport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.NonexceptionalLedger
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.MarkedHighLedger
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The facts of one row of the selected low columns that pay its returned HIGH part: the missing radical of the first
label, the side of the label, and the first-level payment of the coordinates of the row with the uniform shift of the
side. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
open CenteredMomentFirstCanonicalAllowance CenteredMomentCommonHarmonicMass
open Cycle63FinalCapacity CenteredMomentFirstPhysicalSource CenteredMomentAmplificationChildSourceCaps

/-- The missing radical of a first label has a log norm in `[0, Bnorm]` when the first ideal has norm at most
`Z^Bnorm`. -/
theorem facts_missing_bounds (left : Bool) (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (Z Bnorm : ℝ) (hZ : 1 < Z) (hnorm : (l.1.1.absNorm : ℝ) ≤ Z ^ Bnorm) :
    0 ≤ Real.logb Z ((firstSourceMissing left l).absNorm : ℝ) ∧
      Real.logb Z ((firstSourceMissing left l).absNorm : ℝ) ≤ Bnorm := by
  obtain ⟨hpos, hle, -⟩ := first_missing_norm_le left l hC hD
  have hposR : (0 : ℝ) < ((firstSourceMissing left l).absNorm : ℝ) := by exact_mod_cast hpos
  refine ⟨Real.logb_nonneg hZ ?_, ?_⟩
  · exact_mod_cast hpos
  · exact (Real.logb_le_iff_le_rpow hZ hposR).mpr ((Nat.cast_le.mpr hle).trans hnorm)

/-- The side of a first label without its first projector: the log norm of its common radical, the exponent
`A - c + R` of the old region, the surplus of the label and the cone surplus. It is the high side of the label less
the log norm of its first projector radical. -/
def lowLabelSide (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) : ℝ :=
  Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm : ℝ) + A -
    Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) +
    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ) +
    max (3 * Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) -
      5 * Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm : ℝ) -
      Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ)) 0 / 6 +
    lowConeSurplus reflected Z l

/-- The exponent of the old region with the surplus of the label is read from the label. -/
theorem lowAllowedExponent_label (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) :
    lowAllowedExponent reflected Z A l =
      A - Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) +
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ) +
        Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm : ℝ) +
        max (3 * Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) -
          5 * Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm : ℝ) -
          Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ)) 0 / 6 := by
  cases reflected
  · simp only [lowAllowedExponent, lowGeometryExponent, lowSurplus, Bool.false_eq_true, ite_false]
  · simp only [lowAllowedExponent, lowGeometryExponent, lowSurplus, ite_true, span_activeConductor_comm l.1.2 l.1.1]

/-- The side of a label without its first projector is at most the bound `p + exponent - log N(seed₀)` when the
common radical has log norm at most `p`, the side exponent of the label is at most `exponent`, and the squarefree
projector `seed₀` divides the first projector radical of the label. -/
theorem lowLabelSide_le (reflected : Bool) (Z A p exponent : ℝ) (l : FirstSourceLabel) (hZ : 1 < Z)
    (hrad : ((commonRadical l.1.1 l.1.2).absNorm : ℝ) ≤ Z ^ p) (hgeom : lowSideExponent reflected Z A l ≤ exponent)
    (seed₀ : Ideal O) (hs₀ : seed₀ ≠ 0) (hdvd : seed₀ ∣ firstProjectorRadical l.1.1 l.1.2 l.2.val)
    (hC : Supported l.1.1) :
    lowLabelSide reflected Z A l ≤ p + exponent - Real.logb Z (seed₀.absNorm : ℝ) := by
  have hrpos : (0 : ℝ) < ((commonRadical l.1.1 l.1.2).absNorm : ℝ) := by
    have : 0 < (commonRadical l.1.1 l.1.2).absNorm := by
      rw [first_common_radical_product]
      exact firstCommonSubsetNorm_pos _ _ hC Finset.univ
    exact_mod_cast this
  have hp : Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm : ℝ) ≤ p :=
    (Real.logb_le_iff_le_rpow hZ hrpos).mpr hrad
  have hEpos : 0 < (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm :=
    firstCommonSubsetNorm_pos _ _ hC l.2.val
  have hsdvd := Nat.le_of_dvd hEpos (map_dvd Ideal.absNorm hdvd)
  have hs0 : (0 : ℝ) < (seed₀.absNorm : ℝ) := by
    have : 0 < seed₀.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs₀)
    exact_mod_cast this
  have hE : Real.logb Z (seed₀.absNorm : ℝ) ≤ Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm : ℝ) :=
    Real.logb_le_logb_of_le hZ hs0 (by exact_mod_cast hsdvd)
  have hside : lowSideExponent reflected Z A l =
      A - Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) +
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ) +
        Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm : ℝ) +
        max (3 * Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) -
          5 * Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm : ℝ) -
          Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ)) 0 / 6 +
        max (lowConeSurplus reflected Z l) 0 := by
    unfold lowSideExponent
    rw [lowAllowedExponent_label]
  have hsur : lowConeSurplus reflected Z l ≤ max (lowConeSurplus reflected Z l) 0 := le_max_left _ _
  unfold lowLabelSide
  linarith only [hp, hE, hside, hsur, hgeom]

/-- The first-level payment of the coordinates of a row, with the uniform shift `σbar` of the side of its label: the
HIGH coordinates `X0 + X1 + ρ X2 + δ X3` of the row at every bin `δ` of the second step are at most the shift plus the
small terms `ω + ε + (1 - Mrow)⁺`, less the reserve of the parent at the row range one, and the amplifier cost of the
amplifier. -/
theorem facts_row_payment (reflected second : Bool) (l : FirstSourceLabel) (hC : Supported l.1.1)
    (hD : Supported l.1.2) (heq : primeSupport l.1.1 = primeSupport l.1.2) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂)
    (hD₂ : Supported D₂) (heq₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (Z δ Mrow A amp ξ reserve ε σbar : ℝ) (hZ : 1 < Z)
    (hδ : Cycle63.Optimization.secondJunction ≤ δ ∧ δ ≤ 3 / 4) (hω : 0 ≤ frequencyLoss Z 32 ξ + reserve)
    (hε : 0 ≤ ε) (hside : lowLabelSide reflected Z A l ≤ σbar) :
    highExponentValue δ (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z Mrow A amp ξ reserve ε) ≤
      σbar + ((frequencyLoss Z 32 ξ + reserve) + ε + max (1 - Mrow) 0) -
        (1 * (1 - Cycle63.Optimization.density δ) - δ * A - amp * Cycle63.Optimization.amplifierCost δ) := by
  have hq0 : Cycle63.Arithmetic.q0 ≤ δ := by
    have h1 := Cycle63.Arithmetic.q0_bounds
    have h2 := Cycle63.Optimization.secondJunction_mem
    linarith [h1.2, h2.1, hδ.1]
  have hδ' : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ 3 / 4 := ⟨hq0, hδ.2⟩
  have hh := actual_high_coordinate_allocation_payment_reserve_E reflected second l hC hD heq C₂ D₂ hC₂ hD₂ heq₂ U Z
    δ Mrow A amp ξ reserve ε hZ hδ'
  dsimp only at hh
  obtain ⟨hρlo, hρhi, -⟩ := Cycle63.Physical.high_density_bounds hδ'
  have hρ0 : 0 ≤ LocalMoment.unmarkedDensity δ := by linarith
  have hρ1 : LocalMoment.unmarkedDensity δ ≤ 1 := by
    have := Cycle63.Arithmetic.rho0_bounds.2
    linarith
  have hγ := Cycle63.Physical.commonRate_nonneg hδ'
  have hc : 0 ≤ Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ) :=
    Real.logb_nonneg hZ (by cases reflected <;> exact norm_ge_one _ (by first | exact hC.1 | exact hD.1))
  have hb₂ : 0 ≤ Real.logb Z ((if second then D₂ else C₂).absNorm : ℝ) :=
    Real.logb_nonneg hZ (by cases second <;> exact norm_ge_one _ (by first | exact hC₂.1 | exact hD₂.1))
  have hγc := mul_nonneg hγ (add_nonneg hc hb₂)
  have h1 : (1 - Mrow) * (1 - LocalMoment.unmarkedDensity δ) ≤ max (1 - Mrow) 0 := by
    rcases le_total (1 - Mrow) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hρ1)]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg h hρ0]
  have h2 : (1 - LocalMoment.unmarkedDensity δ) * (frequencyLoss Z 32 ξ + reserve) ≤
      frequencyLoss Z 32 ξ + reserve := by
    nlinarith [mul_nonneg hρ0 hω]
  have h3 : LocalMoment.unmarkedDensity δ * ε ≤ ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) hε]
  unfold lowLabelSide lowConeSurplus at hside
  unfold Cycle63.Optimization.amplifierCost
  have hd : Cycle63.Optimization.density δ = LocalMoment.unmarkedDensity δ := rfl
  rw [hd]
  linarith only [hh, hside, hγc, h1, h2, h3]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
