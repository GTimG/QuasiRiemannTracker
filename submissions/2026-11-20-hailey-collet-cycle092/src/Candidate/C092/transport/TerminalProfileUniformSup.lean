/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform actual short-profile sup bound, including all positive subunit scales. -/
import Candidate.C092.transport.TerminalProfileUniformEither
set_option autoImplicit false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap
open Set OAI OAI.SevenEighths CenteredMomentFiniteProfileExceptional HeckeDetectorDyadicProfiles

theorem unitProfile_pointwise (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S)
    {C : ℝ} (hC : 1 ≤ C) (W : 𝓢(ℝ,ℂ)) (x : ℝ) : ‖unitProfile S C W x‖ ≤ 1 := by
  exact (SchwartzMap.norm_le_seminorm ℝ (unitProfile S C W) x).trans
    ((Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hS).trans
      ((unitProfile_control S (zero_lt_one.trans_le hC) W).trans (inv_le_one_of_one_le₀ hC)))

/-- Fixed V alone determines the amplitude bound. Both ordinary unit profiles,
all live Fourier parameters, rows and cofactor ratios come afterward. -/
theorem native_short_unit_sup (V : ℝ→ℂ) (hV : Continuous V) :
    ∃ Bv : ℝ, 1 ≤ Bv ∧ ∀ (S : Finset (ℕ×ℕ)), (0,0) ∈ S →
    ∀ C : ℝ, 1 ≤ C → ∀ W : 𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4) →
    ∀ (opened : Bool) (Dstar D : ℝ), 0 < Dstar → 0 ≤ D → D ≤ 4*Dstar →
    ∀ x : ℝ, ‖TerminalActualRow.shortProfile V (unitProfile S C W) opened Dstar D x‖ ≤ Bv := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 9)).bddAbove_image hV.norm.continuousOn
  refine ⟨2+|M|,by linarith [abs_nonneg M],?_⟩
  intro S hS C hC W hs opened Dstar D hDs hD hDc x
  have hpoint := unitProfile_pointwise S hS hC W x
  rw [←actualShort_eq_native]
  cases opened with
  | false => exact hpoint.trans (by linarith [abs_nonneg M])
  | true =>
    change ‖V ((D/Dstar)*x)*unitProfile S C W x‖ ≤ _
    by_cases hw : unitProfile S C W x = 0
    · rw [hw,mul_zero,norm_zero]; positivity
    have hx := ((unitProfile_support S C W).trans hs) hw
    have hr : D/Dstar ∈ Icc (0:ℝ) 4 := ⟨div_nonneg hD hDs.le,(div_le_iff₀ hDs).mpr hDc⟩
    have hxarg : (D/Dstar)*x ∈ Icc (0:ℝ) 9 := by
      constructor
      · exact mul_nonneg hr.1 (by linarith [hx.1])
      · nlinarith [hr.1,hr.2,hx.1,hx.2]
    have hv : ‖V ((D/Dstar)*x)‖ ≤ 2+|M| :=
      (hM (Set.mem_image_of_mem _ hxarg)).trans (by linarith [le_abs_self M])
    rw [norm_mul]
    exact (mul_le_mul hv hpoint (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

#print axioms native_short_unit_sup
end
end QRH.Cycle092.TerminalProfileUniform
