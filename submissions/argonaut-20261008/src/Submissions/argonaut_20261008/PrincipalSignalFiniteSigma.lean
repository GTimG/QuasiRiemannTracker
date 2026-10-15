import Submissions.argonaut_20261008.PrincipalSlotSigma
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal
variable {κ ι : Type*}

structure SlotBoundsSigma (b : ℝ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-b) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

theorem slot_scalar_ne_zero_sigma (b : ℝ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SlotBoundsSigma b S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem slotRatio_error_sigma (b : ℝ)
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBoundsSigma b S T w Q A η P)
    {s : ℂ} (hs : b ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-b) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    weighted_principal_product_error_linear_sigma hblo hbhi S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem slotRatio_bound_sigma (b : ℝ)
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBoundsSigma b S T w Q A η P)
    {s : ℂ} (hs : b ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-b) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [slotRatio_error_sigma b hblo hbhi S T w Q A η h hs]

theorem principalSlot_differentiableAt_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := principal_geometric_bounds_sigma hblo hbhi hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1-coordR Q A s (1/6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1/6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ)^s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1/6) hR hV hD)
    (principal_correction_ne_zero_sigma hblo hbhi hQ hA hη hs)

theorem slotRatio_continuous_line_sigma (b : ℝ)
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SlotBoundsSigma b S T w Q A η P) {a : ℝ} (ha : b ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (principalSlot_differentiableAt_sigma hblo hbhi (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)


theorem principalSlot_differentiableAt_b0 {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hs : (3499999/4000000:ℝ) ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s :=
  principalSlot_differentiableAt_sigma (by norm_num) (by norm_num) hQ hA hη hs

theorem principalSlot_analytic_open_neighborhood {Q : ℝ} {A η : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    AnalyticOnNhd ℂ (principalSlot Q A η) {s : ℂ | (79/100:ℝ) < s.re} := by
  have hd : DifferentiableOn ℂ (principalSlot Q A η)
      {s : ℂ | (79/100:ℝ) < s.re} := by
    intro s hs
    exact (principalSlot_differentiableAt_sigma (b := (79/100:ℝ))
      (by norm_num) (by norm_num) hQ hA hη hs.le).differentiableWithinAt
  exact hd.analyticOnNhd (Complex.isOpen_re_gt _)

theorem b0_in_principalSlot_open_neighborhood {s : ℂ}
    (hs : s.re = (3499999/4000000:ℝ)) : (79/100:ℝ) < s.re := by
  rw [hs]
  norm_num

theorem SlotBoundsSigma.toSlotBounds {b : ℝ} (hb : b ≤ (7/8:ℝ))
    {S : Finset κ} {T : κ → Finset ι} {w Q : κ → ι → ℝ}
    {A η : κ → ι → ℂ} {P : ℝ} (h : SlotBoundsSigma b S T w Q A η P) :
    SlotBounds S T w Q A η P := by
  refine ⟨h.lower, ?_, h.weight_nonneg, h.norm_lower, h.phase_bound, h.target_unit, h.mass_pos⟩
  apply le_trans ?_ h.small
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [h.lower]) (by linarith)) (by norm_num)

/- Contour/kernel/actual normalized-window extensions are outstanding; no claims here. -/
end SevenEighths.PrincipalSignalComparison
end
end OAI

