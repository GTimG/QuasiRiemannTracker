/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentCertificate.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighAssemblyMomentInput
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace SevenEighths.ProbeFinalAssembly
open CenteredMomentEnergyCertifiedExistence
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule

theorem bound_plain_moment_kappa_from_bootstrap
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    2 * HeckeZeroSupremum.beta - 1 ≤ (3 / 4 : ℝ) := by
  linarith

theorem admit_plain_moment_parameters
    (hβ : AsymmetricGeometry.boundary < HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta ∧
      2 * HeckeZeroSupremum.beta - 1 ≤ (3 / 4 : ℝ) := by
  constructor
  · norm_num [AsymmetricGeometry.boundary] at hβ
    linarith
  · exact bound_plain_moment_kappa_from_bootstrap hβhi

theorem perturbed_detector_certified_band
    {gap : ℝ} (D : Parameters.PerturbedHighData gap)
    (F : PerturbedSourceData D)
    (hβ : AsymmetricGeometry.boundary < HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top
      (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ
      0 1 (33 / 50) (33 / 50) 2 (3 / 4) (D.small / 4)
      (count 2 (D.small / 4)) := by
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ
    0 1 (33 / 50) (33 / 50) 2 (3 / 4) (D.small / 4)
  · norm_num
  · intro x hx
    exact F.complex_support (by simpa using hx)
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · norm_num
  · exact div_pos D.small_pos (by norm_num)
  · exact (admit_plain_moment_parameters hβ hβhi).1
  · exact (admit_plain_moment_parameters hβ hβhi).2

end SevenEighths.ProbeFinalAssembly

end

end OAI
