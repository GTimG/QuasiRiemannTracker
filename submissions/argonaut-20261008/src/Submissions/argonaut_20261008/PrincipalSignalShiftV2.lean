import Submissions.argonaut_20261008.PrincipalBoundaryB0
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalShift

/- NEW LOCAL CANDIDATE. Kernel NOT_RUN. Same actual mathematical objects;
   only analytic x boundary and Sigma evidence are adapted. No final estimate assumption. -/
namespace OAI.SevenEighths.LocalPrincipalSignalShiftV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Set MeasureTheory Filter Asymptotics
open HeckeFamily HeckeSignal Continuation
local notation "Id" => Ideal HeckeFamily.O

theorem quotient_holomorphic_pc2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0 < s.re}) {a : ℝ}
    (ha : (analyticBoundaryB0 : ℝ)<a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  exact ((hH.differentiableAt ((Complex.isOpen_re_gt (analyticBoundaryB0)).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem quotient_polynomial_bound_pc2 (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, analyticBoundaryB0<s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (n : ℕ) (ha : (analyticBoundaryB0 : ℝ)<a) (_hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ 2) :
    ‖quotient χ H s‖ ≤ ((3/2)*C)*(1+|s.im|^n) := by
  have hnorm : ‖H s‖ ≤ 3/2 := by
    have ht := norm_add_le (H s-1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith [hb s (ha.trans_le hs.1)]
  unfold quotient
  rw [norm_mul]
  calc
    _ ≤ (3/2)*(C*(1+|s.im|^n)) :=
      mul_le_mul hnorm (hR s hs.1 hs.2) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem contour_shift_left_pc2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0<s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (analyticBoundaryB0 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ n ha2
    (gaussianContourIntegrand_differentiableOn (quotient_holomorphic_pc2 χ H hH ha hβ) c hx0)
    (C := x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*((3/2)*C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x^(b+c) ≤ x^(2+c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have h5 : (5 / 6 : ℝ) < b :=
    fiveSixths_lt_analyticBoundaryB0.trans
      (ha.trans_le hb'.1)
  have he : Real.exp ((b-5/6)^2) ≤ Real.exp ((2-5/6 : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [h5, hb'.2]
  have hq := quotient_polynomial_bound_pc2 χ H hb n ha hC hR
    (s := (b : ℂ)+y*I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)) *
        (((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring

theorem signal_bound_at_infinity_pc2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0<s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (analyticBoundaryB0 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    ‖signal χ H c x‖ ≤ HeckeSignalShift.infinityConstant a C n*x^(a+c) := by
  have hx0 : 0 < x := by linarith
  rw [contour_shift_left_pc2 χ H hH hb c a C n ha ha2 hβ hC hR hx, norm_mul]
  have hint := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable n).const_mul
      (x^(a+c)*Real.exp ((a-5/6)^2)*((3/2)*C)))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
      have hq := quotient_polynomial_bound_pc2 χ H hb n ha hC hR
        (s := (a : ℂ)+y*I) (by simpa using And.intro (le_refl a) ha2)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
      calc
        _ ≤ x^(a+c)*Real.exp ((a-5/6)^2)*(((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
        _ = _ := by unfold polynomialGaussian; ring))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 ; unfold HeckeSignalShift.infinityConstant ; ring

theorem signal_isBigO_atTop_pc2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0<s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (analyticBoundaryB0 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n)) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  apply IsBigO.of_bound (HeckeSignalShift.infinityConstant a C n)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := signal_bound_at_infinity_pc2 χ H hH hb c a C n ha ha2 hβ hC hR hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ x by linarith) (a+c))] using h


end
end OAI.SevenEighths.LocalPrincipalSignalShiftV2
