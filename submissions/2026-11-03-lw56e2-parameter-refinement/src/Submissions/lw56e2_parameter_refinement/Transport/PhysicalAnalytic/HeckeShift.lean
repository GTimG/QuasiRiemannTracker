/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalAnalytic/HeckeShift.lean
Original SHA-256: 3b080a8117fbb61485f47199c5c417b62564b23b46aa3acce07191ba4baaf8e8
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.TunedCandidate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalBounds

namespace LW56e2.Transport.PhysicalAnalytic.HeckeShift
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI OAI.SevenEighths
open HeckeFamily HeckeSignal Continuation
abbrev transportBoundary : ℝ := Geometry.boundary TunedCandidate.p

theorem quotient_holomorphic (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | transportBoundary < s.re}) {a : ℝ}
    (ha : (transportBoundary : ℝ)<a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  have hboundary : (4/5 : ℝ) < transportBoundary := by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  intro s hs
  exact ((hH.differentiableAt ((Complex.isOpen_re_gt (transportBoundary)).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem quotient_polynomial_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, transportBoundary<s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (n : ℕ) (ha : (transportBoundary : ℝ)<a) (_hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ 2) :
    ‖quotient χ H s‖ ≤ ((3/2)*C)*(1+|s.im|^n) := by
  have hboundary : (4/5 : ℝ) < transportBoundary := by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
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

theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | transportBoundary<s.re})
    (hb : ∀ s : ℂ, transportBoundary<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (transportBoundary : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hboundary : (4/5 : ℝ) < transportBoundary := by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ n ha2
    (gaussianContourIntegrand_differentiableOn (quotient_holomorphic χ H hH ha hβ) c hx0)
    (C := x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*((3/2)*C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x^(b+c) ≤ x^(2+c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have he : Real.exp ((b-5/6)^2) ≤ Real.exp ((2-5/6 : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hb'.1,hb'.2]
  have hq := quotient_polynomial_bound χ H hb n ha hC hR
    (s := (b : ℂ)+y*I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)) *
        (((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring

def infinityConstant (a C : ℝ) (n : ℕ) : ℝ :=
  ‖(1/(2*Real.pi) : ℂ)‖*Real.exp ((a-5/6)^2)*((3/2)*C)*
    ∫ y : ℝ, polynomialGaussian n y

theorem signal_bound_at_infinity (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | transportBoundary<s.re})
    (hb : ∀ s : ℂ, transportBoundary<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (transportBoundary : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    ‖signal χ H c x‖ ≤ infinityConstant a C n*x^(a+c) := by
  have hboundary : (4/5 : ℝ) < transportBoundary := by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  have hx0 : 0 < x := by linarith
  rw [contour_shift_left χ H hH hb c a C n ha ha2 hβ hC hR hx, norm_mul]
  have hint := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable n).const_mul
      (x^(a+c)*Real.exp ((a-5/6)^2)*((3/2)*C)))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
      have hq := quotient_polynomial_bound χ H hb n ha hC hR
        (s := (a : ℂ)+y*I) (by simpa using And.intro (le_refl a) ha2)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
      calc
        _ ≤ x^(a+c)*Real.exp ((a-5/6)^2)*(((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
        _ = _ := by unfold polynomialGaussian; ring))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 ; unfold infinityConstant ; ring

theorem signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | transportBoundary<s.re})
    (hb : ∀ s : ℂ, transportBoundary<s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (transportBoundary : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n)) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  have hboundary : (4/5 : ℝ) < transportBoundary := by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  apply IsBigO.of_bound (infinityConstant a C n)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := signal_bound_at_infinity χ H hH hb c a C n ha ha2 hβ hC hR hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ x by linarith) (a+c))] using h


theorem contour_shift_left_of_beta (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | transportBoundary < s.re})
    (hb : ∀ s : ℂ, transportBoundary < s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : transportBoundary < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hboundary : (4/5 : ℝ) < transportBoundary := by norm_num [transportBoundary, Geometry.boundary, TunedCandidate.p]
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

end
end LW56e2.Transport.PhysicalAnalytic.HeckeShift
