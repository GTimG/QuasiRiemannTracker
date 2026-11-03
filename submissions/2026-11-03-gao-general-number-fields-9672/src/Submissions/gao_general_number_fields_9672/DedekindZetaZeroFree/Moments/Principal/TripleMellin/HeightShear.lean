/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Principal/TripleMellin/HeightShear.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Principal.TripleMellin.HeightPermutationFubini

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory

def heightShear : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun t := ![t 0 + t 2, t 1, t 2]
  invFun t := ![t 0 - t 2, t 1, t 2]
  left_inv t := by ext i; fin_cases i <;> simp
  right_inv t := by ext i; fin_cases i <;> simp
  measurable_toFun := by
    change Measurable (fun t : Fin 3 → ℝ => ![t 0 + t 2, t 1, t 2])
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  measurable_invFun := by
    change Measurable (fun t : Fin 3 → ℝ => ![t 0 - t 2, t 1, t 2])
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop

theorem heightShear_preserving : MeasurePreserving heightShear volume volume := by
  let T : Matrix.TransvectionStruct (Fin 3) ℝ := ⟨0, 2, by decide, 1⟩
  convert Real.volume_preserving_transvectionStruct T using 1
  ext t i
  fin_cases i <;> simp [heightShear, T, Matrix.transvection, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem heightShear_line (t : Fin 3 → ℝ) :
    (5 + ((heightShear t) 0 : ℂ) * Complex.I) =
      (4 + (t 0 : ℂ) * Complex.I) + (2 + (t 2 : ℂ) * Complex.I) - 1 := by
  simp only [heightShear, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Matrix.cons_val_zero,
    Complex.ofReal_add]
  ring

theorem integral_heightShear (f : (Fin 3 → ℝ) → ℂ) :
    (∫ t, f (heightShear t)) = ∫ t, f t :=
  heightShear_preserving.integral_comp' f

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
