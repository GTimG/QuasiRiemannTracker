import Submissions.argonaut_20261008.HighFrontierTargets
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceGeneric

/-!
Source-bound definition equality candidate. Native replay: NOT_RUN.
This file proves no estimate and introduces no analytic hypothesis.
-/
namespace OAI.SevenEighths.LowHighSameProbe

noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbePhysical ProbeRaySlots ProbeFinalAssembly
local notation "O" => HeckeFamily.O

/-- Both definitions use the same actual data, including the total-length normalizer. -/
theorem normalizedProbeAt_eq_generic {N : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    [NeZero (∏ P ∈ S, P)]
    (ell : Fin N → ℝ) (a b : ℝ) (W : Fin N → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Etotal lx ly : ℝ)
    (η : Character) (Z : ℝ) :
    HighFrontierTargets.normalizedProbeAt M H S hS hmax ell a b W W0 W1
      Etotal lx ly η Z =
    normalizedProbeGeneric Etotal lx ly M H S hmax ell a b W W0 W1 η Z := by
  rfl

/-- Function equality, usable directly when transporting an asymptotic statement. -/
theorem normalizedProbeAt_function_eq_generic {N : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    [NeZero (∏ P ∈ S, P)]
    (ell : Fin N → ℝ) (a b : ℝ) (W : Fin N → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Etotal lx ly : ℝ)
    (η : Character) :
    HighFrontierTargets.normalizedProbeAt M H S hS hmax ell a b W W0 W1
      Etotal lx ly η =
    normalizedProbeGeneric Etotal lx ly M H S hmax ell a b W W0 W1 η := by
  rfl

end
end OAI.SevenEighths.LowHighSameProbe
