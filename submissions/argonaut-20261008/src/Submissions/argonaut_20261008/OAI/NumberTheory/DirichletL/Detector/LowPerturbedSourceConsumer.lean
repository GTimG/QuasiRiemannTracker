import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowQuasiPerturbationInstantiation
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowHighSameProbeGeometry

/-!
Additive consumer of the complete returned low quasi interface. Native replay NOT_RUN.
The slot sequence is D.ell throughout. The source/window package is the same F
used by the perturbed high moment construction. No analytic estimate is a premise.
-/
namespace OAI.SevenEighths.LowPerturbedSourceConsumer

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
open HeckeFamily ProbePhysical ProbeFinalAssembly PerturbedMomentConstruction
open LowHighSameProbe
local notation "O" => HeckeFamily.O

/-- The perturbed scalar record supplies the actual total slot length. -/
theorem perturbed_slots_sum_quasi {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B) :
    (∑ j, D.ell j) = QuasiPerturbationParameters.E := by
  simpa only [Parameters.perturbedTotalE, Parameters.perturbedRho,
    QuasiPerturbationParameters.E, QuasiPerturbationParameters.tau] using D.slots_sum

/-- Complete low normalized bound at D.ell, with the actual source/window F. -/
theorem normalizedProbe_low_perturbed {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (loss : ℝ) (hloss : 0 < loss) :
    letI : NeZero (∏ P ∈ F.S, P) :=
      ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    ∀ η : Character,
      normalizedProbeGeneric QuasiPerturbationParameters.E
        QuasiPerturbationParameters.lx QuasiPerturbationParameters.ly
        F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W η
        =O[atTop] (fun Z : ℝ =>
          Z ^ (QuasiPerturbationParameters.sigma - 11 / 16 + loss)) := by
  letI : NeZero (∏ P ∈ F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  exact normalizedProbe_low_quasi F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss
    D.ell (fun j => (D.slots_bounds j).1) D.slots_injective
    (perturbed_slots_sum_quasi D)
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact)
    (fun _ => F.support) (fun _ => F.bounded) (fun _ => F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real
    F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero

/-- Source count constants live on the same modulus, subgroup and actual D.t. -/
theorem source_count_parameters_at_perturbed {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine)) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact source_count_parameters (momentGeometryOfPerturbed D hfine) F

/-- Transport the low bound to the exact high-parent normalized function. -/
theorem normalizedProbeAt_low_perturbed {Δ B : ℝ}
    (D : Parameters.HighDataPerturbedBudget Δ B)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ η : Character,
      HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions F.maximal
        (momentGeometryOfPerturbed D hfine).ell 1 2 (fun _ => F.w) F.W F.W
        HighFrontierTargets.totalE HighFrontierTargets.lx HighFrontierTargets.ly η
        =O[atTop] (fun Z : ℝ =>
          Z ^ (HighFrontierTargets.sigmaBoundary - 11 / 16 + loss)) := by
  letI : NeZero (∏ P ∈ F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  intro η
  rw [normalizedProbeAt_geometry_eq_quasi D hfine F η]
  exact normalizedProbe_low_perturbed D hfine F loss hloss η

end
end OAI.SevenEighths.LowPerturbedSourceConsumer
