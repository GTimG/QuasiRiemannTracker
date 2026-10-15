import Submissions.argonaut_20261008.PrincipalBoundaryB0
import Submissions.argonaut_20261008.PrincipalProductSigma
import Submissions.argonaut_20261008.FullGlobalCorrection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison

namespace OAI.SevenEighths.LocalPrincipalCutoffsV2
noncomputable section
open HeckeFamily ProbePhysical ProbeEuler PrincipalSignalComparison

def productCutoff : ℕ := Classical.choose exists_uniform_principal_cutoff_tau
def globalCutoff : ℕ := Classical.choose exists_uniform_global_sigma_cutoff
def commonCutoff : ℕ := max productCutoff globalCutoff

theorem same_source_tail (S : Finset (Ideal HeckeFamily.O))
    (hcut : ∀ P : PrimeIdeal, P.val.absNorm ≤ commonCutoff → P.val ∈ S) :
    CorrectionTailSigma S := by
  apply (Classical.choose_spec exists_uniform_global_sigma_cutoff).2 S
  intro P hP
  exact hcut P (hP.trans (le_max_right _ _))

theorem same_source_exclusions (S : Finset (Ideal HeckeFamily.O))
    (hS : SourceExclusions S)
    (hcut : ∀ P : PrimeIdeal, P.val.absNorm ≤ commonCutoff → P.val ∈ S) :
    SourceExclusionsSigma S :=
  ⟨hS.prime, hS.bad, same_source_tail S hcut⟩

theorem same_source_correction (S : Finset (Ideal HeckeFamily.O))
    (hS : SourceExclusions S)
    (hcut : ∀ P : PrimeIdeal, P.val.absNorm ≤ commonCutoff → P.val ∈ S)
    (eta : Character) :
    AnalyticOnNhd ℂ (sourceCorrection eta S) {s : ℂ | analyticBoundaryB0 < s.re} ∧
      ∀ s : ℂ, analyticBoundaryB0 < s.re → ‖sourceCorrection eta S s - 1‖ ≤ 1 / 2 := by
  have hproduct := (Classical.choose_spec exists_uniform_principal_cutoff_tau).2 S
    (fun P hP => hcut P (hP.trans (le_max_left _ _))) eta
  have heq := sourceCorrection_eq_principal eta S hS
  simpa only [heq, analyticBoundaryB0] using hproduct

/-- Legitimate new-region local inverse; the input is Sigma, not old tail. -/
theorem correction_lower_bound (eta : Character) (S : Finset (Ideal HeckeFamily.O))
    (hS : CorrectionTailSigma S) (P : PrimeIdeal) (hP : P.val ∉ S)
    (x w z : ℂ) (hx : analyticBoundaryB0 ≤ x.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    (1 / 2 : ℝ) ≤ ‖idealClosedCorrection eta P x w z‖ := by
  have hb := (idealClosedCorrection_sigma_bound eta P (hS.norm_four P hP) x w z
    ((by norm_num : (87 / 100 : ℝ) ≤ analyticBoundaryB0).trans hx)
    (by linarith) (by linarith)).trans (hS.half ⟨P, hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection eta P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem global_norm_bound (eta : Character) (S : Finset (Ideal HeckeFamily.O))
    (hS : CorrectionTailSigma S) (x w z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : (19 / 20 : ℝ) ≤ w.re)
    (hz : (33 / 200 : ℝ) ≤ z.re) : ‖globalClosedCorrection eta S x w z‖ ≤ 3 / 2 := by
  have hb := globalClosedCorrection_sigma_bound eta S hS x w z
    ((by norm_num : (87 / 100 : ℝ) ≤ analyticBoundaryB0).trans hx)
    (by linarith) (by linarith)
  have hn := norm_add_le (globalClosedCorrection eta S x w z - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith

end
end OAI.SevenEighths.LocalPrincipalCutoffsV2
