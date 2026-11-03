/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalRatio.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighSlotEstimate
import Submissions.crossnox_perturbed_boundary.OAIHighSignalShift
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
variable {κ ι : Type*}

def asymmetricKernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) signalOffset Z ((a : ℂ)+t*I)

def asymmetricKernelEnvelope (a C Z : ℝ) : ℝ :=
  Z^(a+signalOffset) * Real.exp ((a-5/6)^2) * ((3/2)*C)

def asymmetricSlotResidue (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)+(signalOffset : ℂ)) *
      Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
      H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I)

theorem asymmetricSlotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    asymmetricSlotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      asymmetricKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold asymmetricSlotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [asymmetricKernel, gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  ring

theorem asymmetric_raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => asymmetricKernel χ H a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)+(signalOffset : ℂ)) *
        Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  unfold asymmetricKernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  ring

theorem weighted_principal_slot_error_on_perturbed_boundary
    {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1)
    (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : perturbedBoundary ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
      (∑ i ∈ S, w i : ℝ)‖ ≤
        (1440 * P ^ (-perturbedBoundary)) * ∑ i ∈ S, w i := by
  apply weighted_slot_error S w _ _ hw
  intro i hi
  have hslot := bound_region_slot_error_on_perturbed_boundary
    (w := (1 : ℂ)) (z := (1 / 6 : ℂ))
    (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs
    (by norm_num) (by norm_num)
  rw [region_slot_at_residue] at hslot
  apply hslot.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi)
    (by unfold perturbedBoundary; norm_num)

theorem slotRatio_error_on_perturbed_boundary
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    (hsmall : 1440 * P ^ (-perturbedBoundary) ≤ 1)
    {s : ℂ} (hs : perturbedBoundary ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤
      slotErrorConstant S * P ^ (-perturbedBoundary) := by
  change ‖(∏ j ∈ S, ∑ i ∈ T j,
    (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
      PrincipalSlotEstimate.principalScalar S
        (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤ _
  have hP0 : 0 ≤ P := by linarith [h.lower]
  have hlinear := fixed_product_relative_error_linear S
    (fun j => ∑ i ∈ T j, w j i)
    (fun j => ∑ i ∈ T j,
      (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s)
    (1440 * P ^ (-perturbedBoundary))
    (by positivity) hsmall h.mass_pos
    (fun j hj => weighted_principal_slot_error_on_perturbed_boundary
      (T j) (w j) (Q j) (A j) (η j) s P h.lower
      (h.weight_nonneg j hj) (h.norm_lower j hj)
      (h.phase_bound j hj) (h.target_unit j hj) hs)
  simpa only [slotErrorConstant, mul_assoc] using hlinear

theorem slotRatio_bound_on_perturbed_boundary
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    (hsmall : 1440 * P ^ (-perturbedBoundary) ≤ 1)
    {s : ℂ} (hs : perturbedBoundary ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤
      1 + slotErrorConstant S * P ^ (-perturbedBoundary) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [slotRatio_error_on_perturbed_boundary S T w Q A η h hsmall hs]

theorem principalSlot_differentiableAt_on_perturbed_boundary
    {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hs : perturbedBoundary ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hV := bound_region_geometric_factors_on_perturbed_boundary
    (w := (1 : ℂ)) (z := (1 / 6 : ℂ))
    hQ hη hs (by norm_num) (by norm_num)
  have hD := one_sub_ne_zero_of_norm_le_half _ hV.2.2
  have hV' := one_sub_ne_zero_of_norm_le_half _ hV.1
  have hR : 1 - coordR Q A s (1 / 6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1 / 6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    unfold perturbedBoundary at hs
    norm_num [boundary] at hs
    linarith
  have hcorr := bound_region_correction_defect_on_perturbed_boundary
    (w := (1 : ℂ)) (z := (1 / 6 : ℂ))
    hQ hA hη hs (by norm_num) (by norm_num)
  have hne : unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
    apply norm_pos_iff.mp
    have hn := norm_sub_norm_le (1 : ℂ)
      (unramifiedClosed Q A η 1 s 1 (1 / 6))
    rw [norm_one, norm_sub_rev] at hn
    linarith
  have hr := coordR_differentiable Q hQ0 A (1 / 6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ) ^ s) :=
    (differentiable_id.const_cpow (Or.inl hQnz)).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div
    (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1 / 6)
      hR hV' hD) hne

theorem slotRatio_continuous_line_on_perturbed_boundary
    (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SlotBounds S T w Q A η P)
    {a : ℝ} (ha : perturbedBoundary ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ) + t * I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ =>
        principalSlot (Q j p) (A j p) (η j p) ((a : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (principalSlot_differentiableAt_on_perturbed_boundary
      (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

end SevenEighths.PrincipalSignalComparison

end

end OAI
