/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighAssemblyFinal.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighAssemblyFixedHigh
import Submissions.crossnox_perturbed_boundary.OAIHighCommonProbe
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalActualBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyChosenData

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open PrincipalSignalComparison HeckeSignal HeckeCommonProbe

theorem actual_source_analytic_on_perturbed_boundary
    (S : Finset (Ideal HeckeFamily.O))
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (η : Character) :
    (∀ I, idealCoeff (η.excludePrimes S hS.prime) I =
      if IsCoprime I (η.excludePrimes S hS.prime).modulus
      then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S)
      {s : ℂ | HeckeSignal.perturbedBoundary < s.re} ∧
    (∀ s : ℂ, HeckeSignal.perturbedBoundary < s.re →
      ‖sourceCorrection η S s - 1‖ ≤ 1 / 2) := by
  refine ⟨excludePrimes_mask η S hS.prime, ?_, ?_⟩
  · have h := sourceCorrection_differentiable_on_perturbed_boundary η S hTail
    apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
    simpa only [HeckeSignal.perturbedBoundary,
      PrincipalSlotEstimate.perturbedBoundary] using h
  · intro s hs
    apply sourceCorrection_bound_on_perturbed_boundary η S hTail s
    simpa only [HeckeSignal.perturbedBoundary,
      PrincipalSlotEstimate.perturbedBoundary] using hs

theorem beta_le_seven_eighths_from_chosen_moments
    (hchosen : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ 7 / 8 :=
  HeckeCommonProbe.beta_le_seven_eighths
    (common_probe_of_chosen_moments hchosen)

theorem common_perturbed_probe_of_chosen_moments
    (hmom : ChosenPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    UniformPerturbedCommonProbe := by
  intro hβ
  obtain ⟨D, F, counts, J, hJ, hbound⟩ := hmom hβ
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, hsource⟩ :=
    perturbed_chosen_data_height D F counts J hJ hbound
  obtain ⟨C, hC, hhigh⟩ :=
    fixed_perturbed_high_bound hβ hβhi D F counts τ
      hτ hτd hτcost hτt hτ2 hτeps
  let ω := (HeckeZeroSupremum.beta - HeckeSignal.perturbedBoundary) / 2
  have hω0 : 0 < ω := by dsimp [ω]; linarith
  have hω : ω < HeckeZeroSupremum.beta - HeckeSignal.perturbedBoundary := by
    dsimp [ω]
    linarith
  refine ⟨ω, D.sigma, hω0, hω, D.sigma_pos, ?_⟩
  intro η hprimitive
  obtain ⟨hmask, hH, hHbound⟩ :=
    actual_source_analytic_on_perturbed_boundary F.S F.exclusions
      F.correction_tail η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,
    sourceCorrection η F.S, F.probe η,
    hmask, hH, hHbound, ?_, ?_⟩
  · have hlow := F.probe_low AsymmetricGeometry.lowAllowance (by norm_num) η
    apply hlow.trans
    apply Continuation.rpow_isBigO_atTop_of_le
    change AsymmetricGeometry.lowBase - AsymmetricGeometry.lengthShift / 4 +
      AsymmetricGeometry.lowAllowance ≤
        AsymmetricGeometry.boundary + AsymmetricGeometry.signalOffset + ω
    exact AsymmetricGeometry.bound_low_allowance.le.trans
      (le_add_of_nonneg_right hω0.le)
  · obtain ⟨Ct, hCt, hhigh⟩ := hhigh η
    obtain ⟨Cm, hCm, hsource⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct + C * Cm * (η.modulus.absNorm : ℝ) ^ (2 * D.eps),
      by positivity, ?_⟩
    filter_upwards [hhigh, hsource] with Z hh hs
    exact hh Cm hCm.le hs

theorem common_perturbed_probe_of_raw_moments
    (hmom : RawPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    UniformPerturbedCommonProbe :=
  common_perturbed_probe_of_chosen_moments
    (chosen_perturbed_input_of_raw hmom) hβhi

theorem beta_le_perturbed_boundary_of_chosen_perturbed_moments
    (hmom : ChosenPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    HeckeZeroSupremum.beta ≤ HeckeSignal.perturbedBoundary :=
  HeckeCommonProbe.beta_le_perturbed_boundary
    (common_perturbed_probe_of_chosen_moments hmom hβhi)

theorem beta_le_perturbed_boundary_of_fine_moments
    (hmom : FinePerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    HeckeZeroSupremum.beta ≤ HeckeSignal.perturbedBoundary :=
  beta_le_perturbed_boundary_of_chosen_perturbed_moments
    (chosen_perturbed_input_of_fine hmom) hβhi

theorem beta_le_perturbed_boundary_of_raw_moments
    (hmom : RawPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    HeckeZeroSupremum.beta ≤ HeckeSignal.perturbedBoundary :=
  HeckeCommonProbe.beta_le_perturbed_boundary
    (common_perturbed_probe_of_raw_moments hmom hβhi)

theorem beta_le_perturbed_boundary_of_raw_and_chosen_moments
    (hmom : RawPerturbedMomentInput) (hchosen : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ HeckeSignal.perturbedBoundary :=
  beta_le_perturbed_boundary_of_raw_moments hmom
    (beta_le_seven_eighths_from_chosen_moments hchosen)

theorem hecke_of_chosen_perturbed_moments
    (hmom : ChosenPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (χ : Character) (s : ℂ)
    (hs : HeckeSignal.perturbedBoundary < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  HeckeCommonProbe.hecke_ne_zero_of_perturbed_common_probe
    (common_perturbed_probe_of_chosen_moments hmom hβhi) χ s hs hpole

theorem dirichlet_of_chosen_perturbed_moments
    (hmom : ChosenPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : HeckeSignal.perturbedBoundary < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  letI : NeZero q := ⟨hq⟩
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h, HeckeSignal.perturbedBoundary] at hs
  have h := hecke_of_chosen_perturbed_moments hmom hβhi
    (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_of_chosen_perturbed_moments
    (hmom : ChosenPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (s : ℂ) (hs : HeckeSignal.perturbedBoundary < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_of_chosen_perturbed_moments hmom hβhi
    1 (by norm_num) (1 : DirichletCharacter ℂ 1) s hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

theorem hecke_of_raw_perturbed_moments
    (hmom : RawPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (χ : Character) (s : ℂ)
    (hs : HeckeSignal.perturbedBoundary < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  hecke_of_chosen_perturbed_moments
    (chosen_perturbed_input_of_raw hmom) hβhi χ s hs hpole

theorem dirichlet_of_raw_perturbed_moments
    (hmom : RawPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : HeckeSignal.perturbedBoundary < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_of_chosen_perturbed_moments
    (chosen_perturbed_input_of_raw hmom) hβhi q hq χ s hs hexc

theorem zeta_of_raw_perturbed_moments
    (hmom : RawPerturbedMomentInput)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (s : ℂ) (hs : HeckeSignal.perturbedBoundary < s.re) :
    riemannZeta s ≠ 0 :=
  zeta_of_chosen_perturbed_moments
    (chosen_perturbed_input_of_raw hmom) hβhi s hs

end SevenEighths.ProbeFinalAssembly

end

end OAI
