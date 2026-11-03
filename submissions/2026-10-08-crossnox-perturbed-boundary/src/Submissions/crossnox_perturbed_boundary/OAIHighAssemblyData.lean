/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighAssemblyData.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighData
import Submissions.crossnox_perturbed_boundary.OAIHighFixedSource
import Submissions.crossnox_perturbed_boundary.OAILowNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

structure PerturbedSourceData {gap : ℝ} (D : PerturbedHighData gap) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀ P ∈ S, P.IsMaximal
  first : FirstTail (4 * D.e) S
  correction_tail : PerturbedCorrectionTail S
  w : ℝ → ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w ⊆ Set.Ioo 1 2
  positive_support : tsupport w ⊆ Set.Ioi 0
  bounded : ∀ x, 0 ≤ w x ∧ w x ≤ 1
  nonzero : w ≠ 0
  complex_eq : ∀ x, W x = (w x : ℂ)
  complex_nonzero : W ≠ 0
  complex_support : Function.support W ⊆ Set.Icc 1 2
  real : ∀ x, (W x).im = 0
  nonnegative : ∀ x, 0 ≤ (W x).re

theorem exists_perturbed_source_data {gap : ℝ} (D : PerturbedHighData gap) :
    Nonempty (PerturbedSourceData D) := by
  obtain ⟨S, _, hS, hfirst, htail, hmax⟩ :=
    exists_fixed_source_on_perturbed_boundary D.e D.e_pos ∅ (by simp)
  obtain ⟨w, W, hw, hc, hs, hp, hb, hn, he, hWn, hWs, hr, hWpos⟩ :=
    exists_fixed_probe_window
  exact ⟨⟨S, hS, hmax, hfirst, htail, w, W, hw, hc, hs, hp, hb,
    hn, he, hWn, hWs, hr, hWpos⟩⟩

def PerturbedSourceData.modulus {gap : ℝ} {D : PerturbedHighData gap}
    (F : PerturbedSourceData D) : Ideal O := ∏ P ∈ F.S, P

instance {gap : ℝ} {D : PerturbedHighData gap} (F : PerturbedSourceData D) :
    NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {gap : ℝ} {D : PerturbedHighData gap} (F : PerturbedSourceData D) :
    Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem perturbed_source_count_parameters {gap : ℝ} {D : PerturbedHighData gap}
    (F : PerturbedSourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.small) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num)
    F.support (fun x => (F.bounded x).2) D.small D.small_pos

def perturbedNormalizedProbe {K : ℕ} (M : Ideal O) [NeZero M]
    [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hmax : ∀ P ∈ S, P.IsMaximal)
    [NeZero (∏ P ∈ S, P)] (ell : Fin K → ℝ) (a b : ℝ)
    (W : Fin K → ℝ → ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (η : Character) (Z lengthShift : ℝ) : ℂ :=
  let Yp := fun j => Z ^ (ell j)
  let T := fun j => pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j => canonicalSlotSupport (T j))
    (fun j y => (W j y : ℂ)) Yp
    (Z ^ (AsymmetricGeometry.xBase - lengthShift / 2))
    (Z ^ (AsymmetricGeometry.yBase - lengthShift / 2)) Z /
    (sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
      (Probe.principalScalar Finset.univ Z (1 / 6 + lengthShift)
        (slotMass T (residueWeights W Yp)) : ℂ))

def PerturbedSourceData.probe {gap : ℝ} {D : PerturbedHighData gap}
    (F : PerturbedSourceData D) (η : Character) : ℝ → ℂ :=
  letI : NeZero (∏ P ∈ F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  fun Z => perturbedNormalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2
    (fun _ => F.w) F.W F.W η Z perturbedSlotLengthShift

theorem PerturbedSourceData.probe_low {gap : ℝ} {D : PerturbedHighData gap}
    (F : PerturbedSourceData D) (loss : ℝ) (hloss : 0 < loss)
    (η : Character) :
    F.probe η =O[atTop]
      (fun Z : ℝ => Z ^ (AsymmetricGeometry.lowBase - perturbedSlotLengthShift / 4 + loss)) := by
  let : NeZero (∏ P ∈ F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  obtain ⟨C, hC, hbound⟩ :=
    perturbed_original_normalized_compensatedPhysicalProbe_low
      F.modulus ⊤ le_top F.S F.exclusions F.maximal
      1 2 1 loss (by norm_num) (by norm_num) hloss D.ell
      (fun j => (D.slots_bounds j).1) D.slots_injective
      perturbedSlotLengthShift (by dsimp [perturbedSlotLengthShift]; norm_num)
      (by dsimp [perturbedSlotLengthShift]; norm_num) D.slots_sum
      (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact)
      (fun _ => F.support) (fun _ => F.bounded) (fun _ => F.nonzero)
      F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support F.real F.real
      F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with Z hb
  simpa only [PerturbedSourceData.probe, perturbedNormalizedProbe,
    D.slots_sum] using hb.2

end SevenEighths.ProbeFinalAssembly

end

end OAI
