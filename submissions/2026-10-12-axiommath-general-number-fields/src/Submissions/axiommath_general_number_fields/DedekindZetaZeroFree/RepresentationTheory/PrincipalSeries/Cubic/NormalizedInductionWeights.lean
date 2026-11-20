/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/Cubic/NormalizedInductionWeights.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalPrincipalSeriesNormWeights

theorem exp_mul_log_real {r : ℝ} (hr : 0 < r) (a : ℝ) :
    Complex.exp ((a : ℂ) * (Real.log r : ℂ)) = (r ^ a : ℝ) := by
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp,
    Real.rpow_def_of_pos hr, mul_comm]

theorem absolute_pow {U : Type*} [Monoid U] (R : U → ℝ)
    (h1 : R 1 = 1) (hm : ∀ x y, R (x * y) = R x * R y)
    (y : U) (n : ℕ) : R (y ^ n) = R y ^ n := by
  induction n with
  | zero => simp [h1]
  | succ n hn => simp [pow_succ, hm, hn]

theorem cube_weights {q : ℝ} (hq : 0 < q) :
    Complex.exp (((1 / 6 : ℝ) : ℂ) * (Real.log ((q ^ (-1 : ℝ)) ^ (3 : ℕ)) : ℂ)) =
      (q ^ (-1 / 2 : ℝ) : ℝ) ∧
    Complex.exp (((1 / 2 : ℝ) : ℂ) * (Real.log ((q ^ (-1 : ℝ)) ^ (3 : ℕ)) : ℂ)) =
      (q ^ (-3 / 2 : ℝ) : ℝ) ∧
    Complex.exp (((1 / 6 : ℝ) : ℂ) * (Real.log (((q ^ (-1 : ℝ))⁻¹) ^ (3 : ℕ)) : ℂ)) =
      (q ^ (1 / 2 : ℝ) : ℝ) := by
  have hr : 0 < q ^ (-1 : ℝ) := Real.rpow_pos_of_pos hq _
  constructor
  · rw [exp_mul_log_real (pow_pos hr _) _, ← Real.rpow_natCast,
      ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
    norm_num
  constructor
  · rw [exp_mul_log_real (pow_pos hr _) _, ← Real.rpow_natCast,
      ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
    norm_num
  · rw [exp_mul_log_real (pow_pos (inv_pos.mpr hr) _) _, ← Real.rpow_neg_one,
      ← Real.rpow_mul hq.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
    norm_num

end DedekindZetaZeroFree.KPLocalPrincipalSeriesNormWeights
