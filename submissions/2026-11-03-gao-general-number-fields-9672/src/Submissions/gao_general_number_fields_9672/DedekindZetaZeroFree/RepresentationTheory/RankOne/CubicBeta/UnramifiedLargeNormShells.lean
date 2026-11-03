/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/RankOne/CubicBeta/UnramifiedLargeNormShells.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalMellin.BallShellPole

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneBetaUnramified.ShellIntegrals

open MeasureTheory IsDedekindDomain NumberField Function
open scoped Classical

theorem geometric_shell_integral {K : Type*} [MeasurableSpace K]
    (ν : Measure K) (shell : ℕ → Set K)
    (hm : ∀ j, MeasurableSet (shell j))
    (hd : Pairwise (Disjoint on shell)) (m : ℝ)
    (hfinite : ∀ j, ν (shell j) ≠ ⊤)
    (hmass : ∀ j, ν.real (shell j) = m)
    (f : K → ℂ) (r : ℂ) (hr : ‖r‖ < 1)
    (hval : ∀ j x, x ∈ shell j → f x = r ^ (j + 1)) :
    IntegrableOn f (⋃ j, shell j) ν ∧
      (∫ x in ⋃ j, shell j, f x ∂ν) = (m : ℂ) * ∑' j : ℕ, r ^ (j + 1) := by
  have hi (j : ℕ) : IntegrableOn f (shell j) ν :=
    (integrableOn_const (hfinite j) (C := r ^ (j + 1))).congr_fun
      (fun x hx => (hval j x hx).symm) (hm j)
  have hin (j : ℕ) : (∫ x in shell j, ‖f x‖ ∂ν) = m * ‖r‖ ^ (j + 1) := by
    rw [setIntegral_congr_fun (hm j) (fun x hx => congrArg norm (hval j x hx)),
      setIntegral_const, hmass, smul_eq_mul, norm_pow]
  have hs : Summable (fun j : ℕ => ‖r‖ ^ (j + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_right ‖r‖
  have hu : IntegrableOn f (⋃ j, shell j) ν :=
    integrableOn_iUnion_of_summable_integral_norm hi (by simpa only [hin] using hs.mul_left m)
  refine ⟨hu, ?_⟩
  rw [integral_iUnion hm hd hu]
  simp_rw [setIntegral_congr_fun (hm _) (hval _), setIntegral_const,
    hmass, Complex.real_smul]
  exact tsum_mul_left

end DedekindZetaZeroFree.KPRankOneBetaUnramified.ShellIntegrals

end
