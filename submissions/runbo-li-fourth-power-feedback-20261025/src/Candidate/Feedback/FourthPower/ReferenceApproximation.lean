/- Copyright (c) 2026 Sil. Apache-2.0.
Actual original-to-retained approximation with an arbitrary saving. The
redundant conductor factor in the pinned baseline is absorbed uniformly.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.ReferenceApproximation
noncomputable section
open scoped Classical ContDiff
open Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalPrimitive CenteredMomentOriginalReflectionApproximation

theorem original_approximation (a b xi saving K L : ℝ)
    (ha : 0 < a) (hxi : 0 < xi) (hK : 0 < K) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ,
      Function.support W ⊆ Icc a b → ContDiff ℝ ∞ W →
      ∃ C : ℝ, 0 < C ∧ ∀ χ : Character, χ.residue ≠ 1 →
      ∃ (ψ : Character) (G : ℂ),
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue ≠ 1 ∧ ‖G‖ = 1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm ≤ χ.modulus.absNorm ∧
        ∀ (X t Z : ℝ), 0 < X → 1 ≤ Z → (χ.modulus.absNorm : ℝ) ≤ Z^K →
          (χ.modulus.absNorm : ℝ) ≤ Z^L*X →
          ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
            G*retainedOriginal χ ψ W X (Z^(xi/2)) t‖ ≤ C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_original_retained_approximation a b xi (saving+1) L 1 (1/K)
    ha hxi (by norm_num) (one_div_pos.mpr hK)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro χ hχ
  obtain ⟨ψ,G,hprim,hne,hG,hcap,he⟩ := hb χ hχ
  refine ⟨ψ,G,hprim,hne,hG,hcap,?_⟩
  intro X t Z hX hZ hmod hscale
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp : (χ.modulus.absNorm : ℝ)^(1/K) ≤ Z := by
    calc
      _ ≤ (Z^K)^(1/K) := Real.rpow_le_rpow (Nat.cast_nonneg _) hmod (one_div_pos.mpr hK).le
      _ = Z := by rw [← Real.rpow_mul hz.le,mul_one_div_cancel hK.ne',Real.rpow_one]
  have hh := he X t Z hX hZ (by simpa only [one_mul] using hscale)
  calc
    _ ≤ C*(χ.modulus.absNorm : ℝ)^(1/K)*(1+‖t‖)^n*Z^(-(saving+1)) := hh
    _ ≤ C*Z*(1+‖t‖)^n*Z^(-(saving+1)) := by gcongr
    _ = C*(1+‖t‖)^n*Z^(-saving) := by
      have hzpow : Z*Z^(-(saving+1)) = Z^(-saving) := by
        conv_lhs => lhs; rw [← Real.rpow_one Z]
        rw [← Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = C*(1+‖t‖)^n*(Z*Z^(-(saving+1))) := by ring
        _ = _ := by rw [hzpow]

end
end Candidate.Feedback.FourthPower.ReferenceApproximation
