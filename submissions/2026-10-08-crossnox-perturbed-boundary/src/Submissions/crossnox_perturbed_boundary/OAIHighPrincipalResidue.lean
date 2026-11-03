/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalResidue.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalRatio

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
variable {κ ι : Type*}

theorem kernel_continuous_on_perturbed_boundary (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | perturbedBoundary < s.re})
    {a Z : ℝ} (ha : perturbedBoundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (asymmetricKernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (HeckeSignalShift.quotient_holomorphic_on_perturbed_boundary χ H hH ha hβ) signalOffset hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound_on_perturbed_boundary (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, perturbedBoundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : perturbedBoundary < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖asymmetricKernel χ H a Z t‖ ≤ asymmetricKernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := HeckeSignalShift.quotient_polynomial_bound_on_perturbed_boundary χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold asymmetricKernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+signalOffset)*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold asymmetricKernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable_on_perturbed_boundary (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | perturbedBoundary < s.re})
    (hb : ∀ s : ℂ, perturbedBoundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : perturbedBoundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (asymmetricKernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (asymmetricKernelEnvelope a C Z)).mono'
    (kernel_continuous_on_perturbed_boundary χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound_on_perturbed_boundary χ H hb ha ha2 hC hZ hR))

theorem slotResidue_bound_of_reciprocal_bound_on_perturbed_boundary (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | perturbedBoundary < s.re})
    (hb : ∀ s : ℂ, perturbedBoundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : perturbedBoundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds S T w Q A η P)
    (hsmall : 1440 * P ^ (-perturbedBoundary) ≤ 1) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => asymmetricKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖asymmetricSlotResidue χ H a Z S T w Q A η - signal χ H signalOffset Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a+signalOffset) * P^(-perturbedBoundary) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := kernel_integrable_on_perturbed_boundary χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := slotRatio_continuous_line_on_perturbed_boundary S T w Q A η h ha.le
  have hbound (t : ℝ) := slotRatio_bound_on_perturbed_boundary S T w Q A η h hsmall
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := slotRatio_error_on_perturbed_boundary S T w Q A η h hsmall
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : asymmetricSlotResidue χ H a Z S T w Q A η - signal χ H signalOffset Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        asymmetricKernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [asymmetricSlotResidue_eq_reciprocal,
      HeckeSignalShift.contour_shift_left_on_perturbed_boundary χ H hH hb
        signalOffset a C 2 ha ha2 hβ hC (fun s hs _ => hR s hs) hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, asymmetricKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, asymmetricKernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change asymmetricKernel χ H a Z t * _ - asymmetricKernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-perturbedBoundary) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖asymmetricKernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (asymmetricKernelEnvelope a C Z * (slotErrorConstant S * P^(-perturbedBoundary))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (asymmetricKernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-perturbedBoundary)) :=
        mul_le_mul (kernel_norm_bound_on_perturbed_boundary χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold asymmetricKernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (asymmetricKernelEnvelope a C Z * (slotErrorConstant S * P^(-perturbedBoundary))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold asymmetricKernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf


end SevenEighths.PrincipalSignalComparison

end

end OAI
