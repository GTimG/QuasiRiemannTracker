/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite Mellin order normalization using the genuine native source seminorm bound. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap
open OAI OAI.SevenEighths CenteredMomentFiniteProfileExceptional

/-- The finite order bank and strip precede the profile. -/
theorem finite_mellin_controls (a b : ℝ) (ha : 0 < a) (lo hi : ℝ)
    (orders : Finset ℕ) :
    ∃ S : Finset (ℕ×ℕ), (0,0) ∈ S ∧ ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ,ℂ), Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b →
      ∀ j ∈ orders, ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin W ((σ:ℂ)+t*Complex.I)‖ ≤ C*sourceControl S W := by
  classical
  induction orders using Finset.induction_on with
  | empty =>
    exact ⟨{(0,0)},by simp,1,zero_lt_one,by simp⟩
  | @insert j orders hj ih =>
    obtain ⟨S,hS,C,hC,hb⟩ := ih
    obtain ⟨T,D,hD,hd⟩ := CubicReflectionKernel.mellin_strip_source_bound a b ha lo hi j
    refine ⟨S ∪ T,Finset.mem_union_left _ hS,C+D,by positivity,?_⟩
    intro W hs k hk σ hσ t
    have hmono (R : Finset (ℕ×ℕ)) (hR : R ⊆ S ∪ T) :
        sourceControl R W ≤ sourceControl (S ∪ T) W := by
      exact Seminorm.le_def.mp (Finset.sup_mono hR) W
    have hs0 := sourceControl_nonneg (S ∪ T) W
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact (hd W hs σ hσ t).trans ((mul_le_mul_of_nonneg_left
        (hmono T Finset.subset_union_right) hD.le).trans (by nlinarith))
    · exact (hb W hs k hk σ hσ t).trans ((mul_le_mul_of_nonneg_left
        (hmono S Finset.subset_union_left) hC.le).trans (by nlinarith))

def unitProfile (S : Finset (ℕ×ℕ)) (C : ℝ) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  C⁻¹ • normalizedProfile S W

theorem unitProfile_control (S : Finset (ℕ×ℕ)) {C : ℝ} (hC : 0 < C)
    (W : 𝓢(ℝ,ℂ)) : sourceControl S (unitProfile S C W) ≤ C⁻¹ := by
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (C⁻¹ • normalizedProfile S W) ≤ C⁻¹
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hC.le)]
  simpa only [sourceControl, mul_one] using mul_le_mul_of_nonneg_left (normalizedProfile_control S W) (inv_nonneg.mpr hC.le)

theorem unitProfile_support (S : Finset (ℕ×ℕ)) (C : ℝ) (W : 𝓢(ℝ,ℂ)) :
    Function.support (unitProfile S C W:ℝ→ℂ) ⊆ Function.support (W:ℝ→ℂ) := by
  intro x hx hw
  apply hx
  simp [unitProfile,normalizedProfile,hw]

theorem unitProfile_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S)
    {C : ℝ} (hC : 0 < C) (W : 𝓢(ℝ,ℂ)) :
    (C*sourceControl S W) • unitProfile S C W = W := by
  rw [unitProfile,smul_smul]
  have he : C*sourceControl S W*C⁻¹ = sourceControl S W := by field_simp
  rw [he,normalizedProfile_reconstruct S hS W]

/-- In particular this handles zero controls without requiring a positive live norm. -/
theorem finite_mellin_unit_profiles (a b : ℝ) (ha : 0 < a) (lo hi : ℝ)
    (orders : Finset ℕ) :
    ∃ S : Finset (ℕ×ℕ), (0,0) ∈ S ∧ ∃ C : ℝ, 0 < C ∧
    ∀ W : 𝓢(ℝ,ℂ), Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b →
      Function.support (unitProfile S C W:ℝ→ℂ) ⊆ Set.Icc a b ∧
      (C*sourceControl S W) • unitProfile S C W = W ∧
      ∀ j ∈ orders, ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (unitProfile S C W) ((σ:ℂ)+t*Complex.I)‖ ≤ 1 := by
  obtain ⟨S,hS,C,hC,hb⟩ := finite_mellin_controls a b ha lo hi orders
  refine ⟨S,hS,C,hC,?_⟩
  intro W hs
  have hsu := (unitProfile_support S C W).trans hs
  refine ⟨hsu,unitProfile_reconstruct S hS hC W,?_⟩
  intro j hj σ hσ t
  exact (hb _ hsu j hj σ hσ t).trans ((mul_le_mul_of_nonneg_left
    (unitProfile_control S hC W) hC.le).trans_eq (mul_inv_cancel₀ hC.ne'))

#print axioms finite_mellin_unit_profiles
end
end QRH.Cycle092.TerminalProfileUniform
