/- The nonunit frequency generator of a live LOW child fits in its nominal width. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.SecondLowGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondRetainedWidth CenteredMomentSecondCanonicalNonunit
open Cycle63FinalLow
open Cycle63FinalNatural Cycle63FinalCapacity
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- The norms of the common and of the nonunit frequency generators of a live row multiply to at most four times the
frequency radius: both divide the frequency of the row, which lies in the retained ball. -/
theorem live_frequency_generators_fit (d : Label → SecondInputDatum α)
    (r : secondLiveRows (fun l => (d l).block)) :
    normValue (commonFrequencyGenerator (d r.val.1).C (d r.val.1).D) *
      normValue (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive) ≤
      4 * (d r.val.1).radius := by
  have hne := actual_second_live_retained_weight (fun l => (d l).block) r.val r.property
  obtain ⟨-, hG, hV, -, -, -, hmax⟩ := retained_geometry (d r.val.1).radius
    (commonFrequencyGenerator (d r.val.1).C (d r.val.1).D)
    (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive) r.val.2.2.2.val hne
  have h := (le_div_iff₀ (mul_pos (normValue_pos _ hG) (normValue_pos _ hV))).mp hmax
  linarith

/-- The logarithms of the norms of the common and of the nonunit frequency generators of a live row add up to at most
the log of the frequency radius plus `log 4`. -/
theorem live_frequency_generators_log (d : Label → SecondInputDatum α)
    (r : secondLiveRows (fun l => (d l).block)) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (commonFrequencyGenerator (d r.val.1).C (d r.val.1).D)) +
      Real.logb Z (normValue (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)) ≤
      Real.logb Z (d r.val.1).radius + Real.logb Z 4 := by
  have hne := actual_second_live_retained_weight (fun l => (d l).block) r.val r.property
  obtain ⟨hR, hG, hV, -, -, -, -⟩ := retained_geometry (d r.val.1).radius
    (commonFrequencyGenerator (d r.val.1).C (d r.val.1).D)
    (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive) r.val.2.2.2.val hne
  have hg := normValue_pos _ hG
  have hv := normValue_pos _ hV
  have hl := Real.logb_le_logb_of_le hZ (mul_pos hg hv) (live_frequency_generators_fit d r)
  rw [Real.logb_mul hg.ne' hv.ne', Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) hR.ne'] at hl
  linarith

/-- The nonunit frequency generator, with the inactive set, of a live LOW child fits in its nominal width up to the
width slack: `ψ ≤ M₁` of the paper, where the unit is the total width of the parent and `hfit` asks the radial
scale and the conductor of the parent to fit in it. -/
theorem live_main_nonunit_width {s : Input α} {q : Chain s} {Z unit Mrow amp omega ξ b εwidth : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hZ : 1 < Z) (hb : 0 < b)
    (hfit : Mrow + Real.logb Z (s.η.modulus.absNorm : ℝ) ≤ unit + (εwidth / 2) * unit)
    (hconstants : Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost +
      2 * (N : ℝ) * Real.logb Z b +
      Real.logb Z (4 * (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)) ≤ (εwidth / 2) * unit) :
    Real.logb Z (normValue (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive)) +
      Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ≤
      secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive +
        (εwidth * unit + ξ / 2) := by
  have hK : 0 < Z ^ Mrow := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hm : g.datum.input.η.modulus = s.η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72 : O)} *
      Ideal.span {primeSubsetGenerator (fun j : CommonIndex g.C₀ g.D₀ => j.val) g.E₀ *
        activeConductor g.C₀ g.D₀} := by
    rw [g.parent]; exact g.hmod
  have hr := main_inverse_radius_log_oriented g.reflected s.η g.datum.input.η g.C₀ g.D₀ g.hC₀ g.hD₀ g.heq₀
    g.E₀ (Z ^ Mrow) (volume s) Z amp g.δ g.reserve ξ b N hK (volume_pos s) hZ hb hm
  dsimp only at hr
  rw [← g.radius_eq] at hr
  have hlive := live_frequency_generators_log (fun _ : Unit => g.datum) g.row Z hZ
  have hmod : 0 ≤ Real.logb Z (g.datum.input.η.modulus.absNorm : ℝ) := by
    rcases Nat.eq_zero_or_pos g.datum.input.η.modulus.absNorm with h | h
    · rw [h]; simp
    · exact Real.logb_nonneg hZ (by exact_mod_cast h)
  have hfixed : (1 : ℝ) ≤ (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ) := by
    exact_mod_cast CenteredMomentSecondRadicalBudget.fixedFactor_pos
  have hfour : Real.logb Z 4 ≤ Real.logb Z (4 * (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)) :=
    Real.logb_le_logb_of_le hZ (by norm_num) (le_mul_of_one_le_right (by norm_num) hfixed)
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hr
  unfold secondNominal LiveMainGeometry.D₁
  rw [g.selected]
  linarith [g.homega]

end
end OAI.SevenEighths.Cycle63InitialMass
