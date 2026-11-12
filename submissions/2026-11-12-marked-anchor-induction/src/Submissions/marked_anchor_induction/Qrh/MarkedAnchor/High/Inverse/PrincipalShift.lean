/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource

/-!
# High.Inverse.PrincipalShift — the dyadic contour shift without nonprincipality

Baseline `HeckeDyadic.finite_rectangle`, `polynomial_finite_shift` and `polynomial_bound_of_rectangle`
take `χ.residue ≠ 1` only to know that `series χ inverse` is holomorphic on the rectangle. Here the
holomorphy is a hypothesis (`hdiff`), so the statements apply to principal characters as well
(for `inverse = true`, `series χ true = reciprocal χ` is holomorphic on `Re s > beta`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse.Principal
noncomputable section

open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic

theorem finite_rectangle_of_diff (χ : Character) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hdiff : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ inverse W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (hdiff s hs)).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ inverse W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift_of_diff (χ : Character) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hdiff : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle_of_diff χ inverse W a b ha hWs hW D σ freq l r T hD hdiff]

theorem polynomial_bound_of_rectangle_of_diff (χ : Character)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hdiff : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      DifferentiableAt ℂ (series χ inverse) (s+shift σ freq))
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift_of_diff χ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hdiff,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end
end Qrh.MarkedAnchor.High.Inverse.Principal

#print axioms Qrh.MarkedAnchor.High.Inverse.Principal.polynomial_bound_of_rectangle_of_diff
