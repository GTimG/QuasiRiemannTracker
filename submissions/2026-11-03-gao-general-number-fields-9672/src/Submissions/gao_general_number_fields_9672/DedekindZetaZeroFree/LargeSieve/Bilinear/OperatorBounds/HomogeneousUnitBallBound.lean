/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Bilinear/OperatorBounds/HomogeneousUnitBallBound.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction
open scoped NumberField Classical

theorem unit_ball_lift
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K A : ℝ) (hA : 0 ≤ A)
    (hform : ∀ lam : Ideal (𝓞 F) → ℂ,
      Q2 F c Q W M N K lam ≤ A * energy F c N lam) :
    B2 F c Q W M N K ≤ A := by
  rw [B2]
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  · rintro x (rfl | ⟨lam, hlam, rfl⟩)
    · exact hA
    · calc Q2 F c Q W M N K lam ≤ A * energy F c N lam := hform lam
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hlam hA
        _ = A := mul_one A

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction

end
