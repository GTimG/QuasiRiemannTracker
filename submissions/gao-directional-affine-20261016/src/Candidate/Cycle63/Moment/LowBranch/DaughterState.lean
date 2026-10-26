import Candidate.Cycle63.Moment.LowBranch.Main
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open QuadraticInitialBound CenteredExceptionalProfile
open CenteredMomentAmplifiedRetainedRadius
local notation "O" => HeckeFamily.O

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

theorem daughterState_width (χ : Character) (Q R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (Z K Bmask bΦ : ℝ) (hZ : 1 < Z) (hK : 1 ≤ K) (hR : R ≠ 0)
    (hRcap : (R.absNorm : ℝ) ≤ Z^Bmask)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) :
    (daughterState χ Q R Φ Z K Bmask bΦ hZ hK hR hRcap hs hp).width =
      Real.logb Z K + Real.logb Z (χ.modulus.absNorm : ℝ) := rfl

/-- The main retained radius gives the literal daughter width. The amplifier
is `sigma/3`, so its contribution here is six times that amplifier. -/
theorem daughter_main_width (χ : Character) (Z d K0 c sigma δ reserve : ℝ)
    (hZ : 1 < Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma δ reserve)+
      Real.logb Z (χ.modulus.absNorm : ℝ) =
    K0+max (d-c) 0+2*sigma+δ+reserve+
      Real.logb Z (χ.modulus.absNorm : ℝ) := by
  rw [mainCommonRadius, Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

#print axioms daughterState
#print axioms daughter_main_width
end
end OAI.SevenEighths.Cycle63Moment.LowBranch
