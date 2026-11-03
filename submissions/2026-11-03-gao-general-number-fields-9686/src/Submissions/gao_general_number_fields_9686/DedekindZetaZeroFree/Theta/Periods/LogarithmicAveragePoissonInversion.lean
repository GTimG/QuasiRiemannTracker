/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/LogarithmicAveragePoissonInversion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.LogarithmicAverageClassInvariance
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.CenteredPoissonSummation

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

theorem topLogIdealAverage_poisson
    (htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    topLogIdealAverage F htop I (1 / t) =
      (t : ℂ) * topLogIdealAverage F htop
        (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I) t := by
  have hpoint (h : RayCoset.logHyperplane F) :
      centeredLogIdealTheta F I (1 / t) h =
        (t : ℂ) * centeredLogIdealTheta F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I) t (-h) := by
    rw [centeredLogIdealTheta_eq_mixedRadialTheta F I (1 / t) (one_div_pos.mpr ht),
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta_poisson F I t ht,
      centeredLogIdealTheta_eq_mixedRadialTheta F _ t ht, map_neg]
  unfold topLogIdealAverage
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  rw [← mul_assoc, mul_comm _ (t : ℂ), mul_assoc]
  congr 1
  exact topLogIdealAverage_reflection F htop _ t ht

end DedekindZetaZeroFree.Hecke.Theta

end
