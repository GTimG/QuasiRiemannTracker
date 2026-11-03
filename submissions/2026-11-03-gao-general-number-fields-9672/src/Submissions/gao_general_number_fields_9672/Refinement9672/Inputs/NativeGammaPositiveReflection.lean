/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Noncircular successor input module, 2026-11-03, Zhongpai Gao with AI assistance.
Apache-2.0. Original theorem/dependency attribution below is retained.
Input module paths are relocated only; declaration namespaces stay original.
The old Hecke endpoint is supplied from the disjoint frozen original proof DAG.
Full native-import checking and successor endpoint verification remain pending.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.Gamma.ShiftAndReflectedRatioBounds

@[expose] public section

namespace DedekindZetaZeroFree

theorem gammaC_reflected_ratio_positive_bound (σ : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, s.re = σ →
      ‖Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K * (2 + |s.im|) := by
  let A : ℝ := Real.Gamma (1 - σ) / Real.Gamma (1 + σ)
  let B : ℝ := (2 * Real.pi) ^ (-(1 - σ)) / (2 * Real.pi) ^ (-σ)
  have hA : 0 < A := div_pos (Real.Gamma_pos_of_pos (by linarith))
    (Real.Gamma_pos_of_pos (by linarith))
  have hbase : 0 < 2 * Real.pi := by positivity
  have hB : 0 < B := div_pos (Real.rpow_pos_of_pos hbase _) (Real.rpow_pos_of_pos hbase _)
  refine ⟨B * A, mul_pos hB hA, fun s hs => ?_⟩
  have hw : (1 - s).re = 1 - σ := by simp [hs]
  have hshift : 1 - s + ((2 * σ : ℝ) : ℂ) = star (s + 1) := by
    apply Complex.ext <;> simp [hs] <;> ring
  have hb := gamma_real_shift_ratio_bound (1 - s) (2 * σ)
    (by rw [hw]; linarith) (by linarith)
  rw [hshift] at hb
  change ‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma ((starRingEnd ℂ) (s + 1))‖ ≤ _ at hb
  rw [Complex.Gamma_conj, Complex.norm_conj, hw] at hb
  have hb' : ‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma (s + 1)‖ ≤ A := by
    convert hb using 1 <;> dsimp [A] <;> congr 2 <;> ring
  have hn : ‖s‖ ≤ 2 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + |s.im| := by rw [hs, abs_of_pos hσ]; linarith
  have hrec : (Complex.Gamma s)⁻¹ = s * (Complex.Gamma (s + 1))⁻¹ := by
    simpa only [one_div] using Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s
  have hg : ‖Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹‖ ≤ A * (2 + |s.im|) := by
    rw [hrec, norm_mul, norm_mul, norm_inv]
    calc _ = (‖Complex.Gamma (1 - s)‖ / ‖Complex.Gamma (s + 1)‖) * ‖s‖ := by ring
      _ ≤ A * (2 + |s.im|) := mul_le_mul hb' hn (norm_nonneg _) hA.le
  have hnorm : ‖Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹‖ =
      B * ‖Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹‖ := by
    simp only [Complex.Gammaℂ_def, norm_mul, norm_inv]
    have he1 : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - s))‖ = (2 * Real.pi) ^ (-(1 - σ)) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp [hs]
    have he2 : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-σ) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      simp [hs]
    rw [he1, he2]
    norm_num
    dsimp [B]
    ring
  rw [hnorm]
  calc B * ‖Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹‖ ≤
      B * (A * (2 + |s.im|)) := mul_le_mul_of_nonneg_left hg hB.le
    _ = _ := by ring

theorem gammaC_reflected_ratio_line_03 :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, s.re = (3 / 100 : ℝ) →
      ‖Complex.Gammaℂ (1 - s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K * (2 + |s.im|) :=
  gammaC_reflected_ratio_positive_bound (3 / 100) (by norm_num) (by norm_num)

#print axioms gammaC_reflected_ratio_positive_bound
#print axioms gammaC_reflected_ratio_line_03

end DedekindZetaZeroFree
