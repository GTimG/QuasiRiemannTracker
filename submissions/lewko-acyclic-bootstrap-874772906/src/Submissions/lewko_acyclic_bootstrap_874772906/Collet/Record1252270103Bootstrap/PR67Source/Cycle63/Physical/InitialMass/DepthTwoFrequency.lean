import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighSelected
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalNatural.State
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoCount
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The norm of the row of a pair of a child prefix and a second-level label, and the row range of the level-two
parent: the second-level frequency coordinate plus the log norm of the child multiplier bounds the row, and the log
row range plus that log norm is the first-level frequency coordinate up to fixed constants. Released under Apache
2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplifiedRetainedRadius
open Cycle63Moment Cycle63HighFrequency Cycle63FinalNatural

/-- The row of a pair of a child prefix and a second-level label has norm at most `Z` to the second-level frequency
coordinate plus the log norm of the prefix multiplier. The threshold precedes the multipliers, their units, the
prefixes and every arithmetic label. -/
theorem eventual_depth_two_row_norm (b ε : ℝ) (N : ℕ) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {P : Type*} (v : P → O) (reflected left second : Bool)
      (unit : P → FirstSourceLabel → Oˣ) (x : NonzeroDepthTwoPair v left (fun p k => (unit p k : O)))
      (_hC : Supported x.val.2.1.1.1) (_hD : Supported x.val.2.1.1.2),
      primeSupport x.val.2.1.1.1 = primeSupport x.val.2.1.1.2 →
      ∀ (V M A a reserve ξ : ℝ), 0 < V → ξ ≤ ε →
      retainedWeight (frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N x.val.2.1) Z ξ)
        (normValue ((commonFrequencyGenerator x.val.2.2.1.1 x.val.2.2.1.2*
          nonunitFrequencyGenerator x.val.2.2.1.1 x.val.2.2.1.2 x.val.2.2.2.val.1)*x.val.2.2.2.val.2)) ≠ 0 →
      0 ≤ actualHighCoordinates reflected left second x.val.2.1 x.val.2.2.1.1 x.val.2.2.1.2 x.val.2.2.2.val.1
          Z M A a ξ reserve ε 2 + Real.logb Z (normValue (v x.val.1)) ∧
        normValue (depthTwoRow v left (fun p k => (unit p k : O)) x.val) ≤
          Z^(actualHighCoordinates reflected left second x.val.2.1 x.val.2.2.1.1 x.val.2.2.1.2 x.val.2.2.2.val.1
            Z M A a ξ reserve ε 2 + Real.logb Z (normValue (v x.val.1))) := by
  filter_upwards [eventual_actual_joint_frequency_budget_uniform b ε N hb hε] with Z hz
  refine ⟨hz.1, ?_⟩
  intro P v reflected left second unit x hC hD heq V M A a reserve ξ hV hξ hret
  have hp := zero_lt_one.trans hz.1
  have hh := hz.2 (v x.val.1) reflected left (unit x.val.1) ⟨x.val.2, x.property⟩ hC hD heq (Z^M) V a
    (frequencyLoss Z 32 ξ) reserve ξ (Real.rpow_pos_of_pos hp M) hV hξ hret
  rw [Real.logb_rpow hp hz.1.ne'] at hh
  simpa [actualHighCoordinates, depthTwoRow, normValue, sub_add_eq_sub_sub] using hh

/-- With unit label factors and a nonzero child multiplier, the log norm of the multiplier is the log norm of the
fixed row plus the log norms of the inactive-set generator, the first numerator, the common frequency generator and
the nonunit frequency generator. -/
theorem logb_normValue_childMultiplier (Z : ℝ) (left : Bool) (u₀ : O) (unit : FirstSourceLabel → Oˣ)
    (p : ChildPrefix) (hv : childMultiplier left u₀ (fun l => (unit l : O)) p ≠ 0) :
    Real.logb Z (normValue (childMultiplier left u₀ (fun l => (unit l : O)) p)) =
      Real.logb Z (normValue u₀) +
        Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val)) +
        Real.logb Z (normValue (firstSourceNumerator left p.1)) +
        Real.logb Z (normValue (commonFrequencyGenerator p.2.1.1 p.2.1.2)) +
        Real.logb Z (normValue (nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2)) := by
  have hv' : (u₀*(unit p.1 : O))*primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val*
      firstSourceNumerator left p.1*
      (commonFrequencyGenerator p.2.1.1 p.2.1.2*nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2) ≠ 0 := hv
  have h₁ := mul_ne_zero_iff.mp hv'
  have h₂ := mul_ne_zero_iff.mp h₁.1
  have h₃ := mul_ne_zero_iff.mp h₂.1
  have h₄ := mul_ne_zero_iff.mp h₃.1
  have h₅ := mul_ne_zero_iff.mp h₁.2
  have pu := normValue_pos _ h₄.1
  have pS := normValue_pos _ h₃.2
  have pF := normValue_pos _ h₂.2
  have pG := normValue_pos _ h₅.1
  have pV := normValue_pos _ h₅.2
  rw [normValue_childMultiplier, Real.logb_mul (mul_pos (mul_pos (mul_pos pu pS) pF) pG).ne' pV.ne',
    Real.logb_mul (mul_pos (mul_pos pu pS) pF).ne' pG.ne', Real.logb_mul (mul_pos pu pS).ne' pF.ne',
    Real.logb_mul pu.ne' pS.ne']

/-- A nonzero row with a nonzero retained weight at the radius `R` puts the second-stage generators inside the
retained radius: the product of their norms is at most `4 R`. -/
theorem retained_generators_fit (R : ℝ) (G V z : O) (hz : z ≠ 0)
    (hret : retainedWeight R (normValue ((G*V)*z)) ≠ 0) :
    normValue G*normValue V ≤ 4*R := by
  have h := (retainedWeight_enclosure R _ hret).2
  rw [normValue_mul, normValue_mul] at h
  have hG : 0 ≤ normValue G := Nat.cast_nonneg _
  have hV : 0 ≤ normValue V := Nat.cast_nonneg _
  calc normValue G*normValue V = normValue G*normValue V*1 := (mul_one _).symm
    _ ≤ normValue G*normValue V*normValue z :=
      mul_le_mul_of_nonneg_left (normValue_ge_one z hz) (mul_nonneg hG hV)
    _ ≤ 4*R := h

/-- When the second-stage generators fit in the retained radius, the log row range of the level-two parent plus the
log norm of the child multiplier is the first-level frequency coordinate less `ε`, plus the log norm of the fixed
row and the fixed presentation constants `log 4 + 2 N log b + ξ/2`. -/
theorem depth_two_scale_identity (reflected left second : Bool) (u₀ : O) (unit : FirstSourceLabel → Oˣ)
    (p : ChildPrefix) (hC : Supported p.1.1.1) (hD : Supported p.1.1.2)
    (heq : primeSupport p.1.1.1 = primeSupport p.1.1.2)
    (hv : childMultiplier left u₀ (fun l => (unit l : O)) p ≠ 0)
    (Z V M A a ξ reserve ε b : ℝ) (N : ℕ) (hZ : 1 < Z) (hV : 0 < V) (hb : 0 < b)
    (hfit : normValue (commonFrequencyGenerator p.2.1.1 p.2.1.2)*
        normValue (nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2) ≤
      4*frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N p.1) Z ξ) :
    Real.logb Z (retainedScale (frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N p.1)
        Z ξ) p.2.1.1 p.2.1.2 p.2.2) +
      Real.logb Z (normValue (childMultiplier left u₀ (fun l => (unit l : O)) p)) =
    actualHighCoordinates reflected left second p.1 p.2.1.1 p.2.1.2 p.2.2 Z M A a ξ reserve ε 2 - ε +
      Real.logb Z (normValue u₀) + (Real.logb Z 4 + 2*(N:ℝ)*Real.logb Z b + ξ/2) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hv' : (u₀*(unit p.1 : O))*primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val*
      firstSourceNumerator left p.1*
      (commonFrequencyGenerator p.2.1.1 p.2.1.2*nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2) ≠ 0 := hv
  have h₁ := mul_ne_zero_iff.mp hv'
  have h₂ := mul_ne_zero_iff.mp h₁.1
  have h₃ := mul_ne_zero_iff.mp h₂.1
  have h₅ := mul_ne_zero_iff.mp h₁.2
  have pG := normValue_pos _ h₅.1
  have pV := normValue_pos _ h₅.2
  have hGV := mul_pos pG pV
  have hRpos : 0 < frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N p.1) Z ξ := by
    linarith
  have hscale : retainedScale (frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N p.1)
      Z ξ) p.2.1.1 p.2.1.2 p.2.2 =
      4*frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N p.1) Z ξ/
        (normValue (commonFrequencyGenerator p.2.1.1 p.2.1.2)*
          normValue (nonunitFrequencyGenerator p.2.1.1 p.2.1.2 p.2.2)) := by
    unfold retainedScale
    exact max_eq_right ((one_le_div hGV).mpr hfit)
  have hS : Ideal.span {primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h₃.2
  have hf : Real.logb Z (frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N p.1) Z ξ) +
      Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val)) +
      Real.logb Z (normValue (activeConductor p.1.1.1 p.1.1.2)) =
      Real.logb Z (Z^M) - max (Real.logb Z ((if reflected then p.1.1.2 else p.1.1.1).absNorm : ℝ) -
        Real.logb Z ((if reflected then p.1.1.1 else p.1.1.2).absNorm : ℝ)) 0 - 2*(3*a) - frequencyLoss Z 32 ξ -
        reserve + 2*(N:ℝ)*Real.logb Z b + ξ/2 :=
    main_fourier_frequency_log reflected p.1.1.1 p.1.1.2 _ hC.1 hD.1 hS heq (Z^M) V Z (3*a)
      (frequencyLoss Z 32 ξ) reserve ξ b N (Real.rpow_pos_of_pos hZ0 M) hV hZ hb
  have hM : Real.logb Z (Z^M) = M := Real.logb_rpow hZ0 hZ.ne'
  have hx2 : actualHighCoordinates reflected left second p.1 p.2.1.1 p.2.1.2 p.2.2 Z M A a ξ reserve ε 2 =
      M - Real.logb Z (normValue (activeConductor p.1.1.1 p.1.1.2)) -
        max (Real.logb Z ((if reflected then p.1.1.2 else p.1.1.1).absNorm : ℝ) -
          Real.logb Z ((if reflected then p.1.1.1 else p.1.1.2).absNorm : ℝ)) 0 +
        Real.logb Z (normValue (firstSourceNumerator left p.1)) - 6*a - (frequencyLoss Z 32 ξ + reserve) + ε :=
    rfl
  rw [hscale, Real.logb_div (mul_pos (by norm_num : (0:ℝ) < 4) hRpos).ne' hGV.ne',
    Real.logb_mul (by norm_num : (4:ℝ) ≠ 0) hRpos.ne',
    Real.logb_mul pG.ne' pV.ne', logb_normValue_childMultiplier Z left u₀ unit p hv, hx2]
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
