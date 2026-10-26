/- Copyright (c) 2026 Sil. Apache-2.0.
Homogeneous ordinary-profile controls for the exact original-to-retained
approximation. All finite controls and constants precede the profile and Z.
The full character modulus is retained, and precisely the original extra-one
tail saving pays its 1/K power. No energy estimate is an input.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceUniformApproximation
noncomputable section
open scoped Classical SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalPrimitive CenteredMomentOriginalReflectionApproximation
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open EisensteinSchwartzPoisson

/-- A single finite homogeneous control for the actual ordinary height twist.
Including `(0,0)` lets consumers handle a zero control by exact vanishing. -/
theorem twisted_source_control (a b : ℝ) (ha : 0 < a)
    (H : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ,
      0 < C ∧ (0,0) ∈ S ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W : ℝ → ℂ) ⊆ Icc a b,
      ∀ t : ℝ,
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (CompletedHeight.uniformTwistedSchwartz W a b ha hs (W.smooth ⊤) t) ≤
        C * sourceControl S W * (1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hcontrol⟩ := normPowerProfile_source_control a b ha H
  let S : Finset (ℕ × ℕ) := T ∪ {(0,0)}
  have hS : (0,0) ∈ S := by simp [S]
  have htwo : 0 < 2*Real.pi := by positivity
  refine ⟨n,S,C*(1+2*Real.pi)^n,by positivity,hS,?_⟩
  intro W hs t
  have hparam : (2*Real.pi*t)/(2*Real.pi) = t := by
    field_simp [htwo.ne']
  have he : normPowerProfile W a b ha hs (W.smooth ⊤) (2*Real.pi*t) =
      CompletedHeight.uniformTwistedSchwartz W a b ha hs (W.smooth ⊤) t := by
    unfold normPowerProfile
    rw [hparam]
  have hT : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ sourceControl S W := by
    exact Seminorm.le_def.mp
      (Finset.sup_mono (Finset.subset_union_left : T ⊆ T ∪ {(0,0)})) W
  have hheight : 1+‖2*Real.pi*t‖ ≤ (1+2*Real.pi)*(1+‖t‖) := by
    rw [norm_mul,Real.norm_of_nonneg htwo.le]
    nlinarith [norm_nonneg t,Real.pi_pos]
  have hb := hcontrol W hs (2*Real.pi*t)
  rw [he] at hb
  calc
    _ ≤ C*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖2*Real.pi*t‖)^n := hb
    _ ≤ (C*sourceControl S W)*((1+2*Real.pi)*(1+‖t‖))^n := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hT hC.le)
        (pow_le_pow_left₀ (by positivity) hheight n) (by positivity)
        (mul_nonneg hC.le (sourceControl_nonneg S W))
    _ = (C*(1+2*Real.pi)^n)*sourceControl S W*(1+‖t‖)^n := by
      rw [mul_pow]
      ring

/-- Uniform, homogeneous replacement for `ReferenceApproximation.original_approximation`.
The primitive character is an actual one supplied by the baseline reflection
identity. In particular no effective-conductor hypothesis replaces the full
modulus cap, and no positivity of the profile control is required. -/
theorem original_approximation (a b xi saving K L : ℝ)
    (ha : 0 < a) (hxi : 0 < xi) (hK : 0 < K) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ,
      0 < C ∧ (0,0) ∈ S ∧
      ∀ W : 𝓢(ℝ,ℂ), Function.support (W : ℝ → ℂ) ⊆ Icc a b →
      ∀ χ : Character, χ.residue ≠ 1 →
      ∃ (ψ : Character) (g : ℂ),
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue ≠ 1 ∧ ‖g‖ = 1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm ≤ χ.modulus.absNorm ∧
        ∀ (X t Z : ℝ), 0 < X → 1 ≤ Z → (χ.modulus.absNorm : ℝ) ≤ Z^K →
          (χ.modulus.absNorm : ℝ) ≤ Z^L*X →
          ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
            g*retainedOriginal χ ψ W X (Z^(xi/2)) t‖ ≤
          C*sourceControl S W*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨H,Ca,hCa,happrox⟩ :=
    CenteredMomentUniformReflectionApproximation.actual_twisted_approximation
      xi (saving+1) L 1 (1/K) hxi (by norm_num) (one_div_pos.mpr hK)
  obtain ⟨n,S,Cp,hCp,hS,hprofile⟩ := twisted_source_control a b ha H
  refine ⟨n,S,Ca*Cp,mul_pos hCa hCp,hS,?_⟩
  intro W hs χ hχ
  obtain ⟨ψ,g,hprim,hne,hg,hcap,he⟩ := happrox χ hχ
  refine ⟨ψ,g,hprim,hne,hg,hcap,?_⟩
  intro X t Z hX hZ hmod hscale
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp : (χ.modulus.absNorm : ℝ)^(1/K) ≤ Z := by
    calc
      _ ≤ (Z^K)^(1/K) := Real.rpow_le_rpow (Nat.cast_nonneg _) hmod
        (one_div_pos.mpr hK).le
      _ = Z := by
        rw [←Real.rpow_mul hz.le,mul_one_div_cancel hK.ne',Real.rpow_one]
  have hh := he W a b ha hs (W.smooth ⊤) t X Z hX hZ
    (by simpa only [one_mul] using hscale)
  have hseminorm := hprofile W hs t
  have hcontrol0 : 0 ≤ sourceControl S W := sourceControl_nonneg S W
  have hzpow : Z*Z^(-(saving+1)) = Z^(-saving) := by
    conv_lhs => lhs; rw [←Real.rpow_one Z]
    rw [←Real.rpow_add hz]
    congr 1
    ring
  calc
    _ ≤ Ca*H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (CompletedHeight.uniformTwistedSchwartz W a b ha hs (W.smooth ⊤) t)*
          (χ.modulus.absNorm : ℝ)^(1/K)*Z^(-(saving+1)) := hh
    _ ≤ (Ca*(Cp*sourceControl S W*(1+‖t‖)^n))*Z*Z^(-(saving+1)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hseminorm hCa.le) hp
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg hCa.le (by positivity))
    _ = (Ca*Cp)*sourceControl S W*(1+‖t‖)^n*Z^(-saving) := by
      calc
        _ = ((Ca*Cp)*sourceControl S W*(1+‖t‖)^n)*(Z*Z^(-(saving+1))) := by ring
        _ = _ := by rw [hzpow]

end
end Candidate.FourthPower.ReferenceUniformApproximation
