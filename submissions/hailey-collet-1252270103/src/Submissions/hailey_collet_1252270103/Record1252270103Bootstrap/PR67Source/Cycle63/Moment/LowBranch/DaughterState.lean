import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.LocalMoment.RestrictedIncumbent
import Mathlib
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical SchwartzMap HeckeNotation
open HeckeFamily ConcretePrimeRowBridge CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open QuadraticInitialBound CenteredExceptionalProfile
open CenteredMomentAmplifiedRetainedRadius

/-- The actual nonexceptional daughter mask. Fixed-inducing daughters remain
in the complementary branch; this definition does not declare them eligible. -/
def daughterKeep (χ : Character) (Q R : Ideal O) (z : O) : Prop :=
  z ≠ 0 ∧ ¬FixedInducingRow χ Q (fixedBadMask*idealGenerator R) 1 z

/-- Exact logarithmic widths of the retained radial cutoff and the actual
character conductor. The puncture is retained literally. -/
def daughterState (χ : Character) (Q R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (Z K Bmask bΦ : ℝ) (hZ : 1 < Z) (hK : 1 ≤ K) (hR : R ≠ 0)
    (hRcap : (R.absNorm : ℝ) ≤ Z^Bmask)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) : NaturalState Z Bmask bΦ where
  character := χ
  fixedModulus := Q
  puncture := R
  radial := {
    keep := daughterKeep χ Q R
    profile := Φ
    scale := K
    scale_pos := zero_lt_one.trans_le hK
    nonneg := fun _ => hp _ }
  rowWidth := Real.logb Z K
  characterWidth := Real.logb Z (χ.modulus.absNorm : ℝ)
  base_ge_one := hZ.le
  row_nonneg := Real.logb_nonneg hZ hK
  character_nonneg := Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
  scale_eq := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (zero_lt_one.trans_le hK)).symm
  modulus_bound := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))]
  puncture_ne_zero := hR
  puncture_bound := hRcap
  radial_support := hs
  row_ne_zero := fun _ h => h.1
  nonexceptional := fun _ h => h.2

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
