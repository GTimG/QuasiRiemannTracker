/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighUnconditional.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighMomentTransport
import Submissions.crossnox_perturbed_boundary.OAIHighAssemblyFinal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

namespace OAI.SevenEighths.PerturbedZeroFree

noncomputable section

open HeckeFamily ProbeFinalAssembly

private theorem identify_boundary :
    HeckeSignal.perturbedBoundary = (4374785349 / 5000000000 : ℝ) := by
  norm_num [HeckeSignal.perturbedBoundary]

theorem prove_prior_boundary : HeckeZeroSupremum.beta ≤ 7 / 8 :=
  beta_le_seven_eighths_from_chosen_moments
    (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
      ProbeFinalAssemblyUnconditional.detector_certified_bands)

theorem prove_chosen_perturbed_moments : ChosenPerturbedMomentInput :=
  chosen_perturbed_input_of_fine
    (PerturbedMomentTransport.prove_fine_perturbed_moments prove_prior_boundary)

theorem bound_zero_supremum :
    HeckeZeroSupremum.beta ≤ (4374785349 / 5000000000 : ℝ) := by
  rw [← identify_boundary]
  exact beta_le_perturbed_boundary_of_chosen_perturbed_moments
    prove_chosen_perturbed_moments prove_prior_boundary

theorem prove_hecke_nonvanishing (χ : Character) (s : ℂ)
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  exact hecke_of_chosen_perturbed_moments
    prove_chosen_perturbed_moments prove_prior_boundary χ s
    (by rwa [identify_boundary]) hpole

theorem prove_dirichlet_nonvanishing (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact dirichlet_of_chosen_perturbed_moments
    prove_chosen_perturbed_moments prove_prior_boundary q hq χ s
    (by rwa [identify_boundary]) hexc

theorem prove_zeta_nonvanishing (s : ℂ)
    (hs : (4374785349 / 5000000000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  exact zeta_of_chosen_perturbed_moments
    prove_chosen_perturbed_moments prove_prior_boundary s
    (by rwa [identify_boundary])

end

end OAI.SevenEighths.PerturbedZeroFree
