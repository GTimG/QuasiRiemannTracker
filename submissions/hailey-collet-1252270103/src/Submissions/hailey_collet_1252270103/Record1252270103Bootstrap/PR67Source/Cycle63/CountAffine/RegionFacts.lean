import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.CountAffine.ClosedForm
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The closed-form count's side conditions on the region and its monotonicity in the prime
amplitude (after the structure of tracker PR #52). Every numerical fact is checked by the
kernel-evaluated Bernstein test `rat_pos` over the region and the enclosure of the bin split.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.CountAffine
noncomputable section
open Cycle63.Arithmetic

/-- The facts of one plain line `a - s m` that the count uses: its closed form `R = 1/6 + V t`,
the crossing `(r, m)` with the inverse line, and the gates on the cutoff, the crossing length and
the window bottom. -/
structure LineFacts (δ x a s t r m R : ℝ) : Prop where
  slope : 0 ≤ s
  closed : R = 1/6 + (5/6-δ)*t
  split : r = t - m
  inverse : inverseLine δ x r = R
  plain : a - s*m = R
  tlo : cutoffFloor ≤ t
  thi : t ≤ 3/2
  rc : crossingFloor ≤ r
  b3 : inverseLine δ x (t - windowBottom) ≤ R

/-- All facts of the two closed forms on the region. -/
structure RegionFacts (δ p : ℝ) : Prop where
  den : 0 < tDen δ p
  sum : 0 < sI δ p + sP δ p
  denC : 0 < tDenC δ p
  sumC : 0 < sI δ p + sPc δ
  affine : LineFacts δ p (aP δ p) (sP δ p) (tStar δ p) (rC δ p) (mC δ p) (RStar δ p)
  capped : LineFacts δ p (aPc δ p) (sPc δ) (tStarC δ p) (rCC δ p) (mCC δ p) (RStarC δ p)

theorem region_mem {δ p : ℝ} (h : inRegion δ p) :
    δ ∈ Set.Icc (43/100:ℝ) (49/100) ∧ p ∈ Set.Icc (495/1000:ℝ) (1/2) :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩

/-- A cutoff bound from its cleared form. -/
theorem le_of_cleared {N D c : ℝ} (hD : 0 < D) (h : 0 < N - c*D) : c ≤ N/D := by
  rw [le_div_iff₀ hD]; linarith

theorem le_of_cleared' {N D c : ℝ} (hD : 0 < D) (h : 0 < c*D - N) : N/D ≤ c := by
  rw [div_le_iff₀ hD]; linarith

/-- The crossing inverse length exceeds `c` when its cleared form is positive. -/
theorem crossing_of_cleared {N D sI' sP' a q c : ℝ} (hD : 0 < D) (hS : 0 < sI' + sP')
    (h : 0 < sP'*N - (c*(sI' + sP') + a - 1 + q)*D) :
    c ≤ N/D - (a - 1 + q + sI'*(N/D))/(sI' + sP') := by
  have hN : N = N/D*D := (div_mul_cancel₀ N hD.ne').symm
  have hfac : sP'*N - (c*(sI' + sP') + a - 1 + q)*D =
      (sP'*(N/D) - (c*(sI' + sP') + a - 1 + q))*D := by
    conv_lhs => rw [hN]
    ring
  rw [hfac] at h
  have key := (mul_pos_iff_of_pos_right hD).mp h
  have hid : N/D - c - (a - 1 + q + sI'*(N/D))/(sI' + sP') =
      (sP'*(N/D) - (c*(sI' + sP') + a - 1 + q))/(sI' + sP') := by
    field_simp
    ring
  have := div_pos key hS
  linarith

/-- The window-bottom gate from its cleared form. -/
theorem window_of_cleared {N D δ q sI' w : ℝ} (hD : 0 < D)
    (h : 0 < (5/6 - δ + sI')*N - (5/6 - q + sI'*w)*D) :
    1 - q - sI'*(N/D - w) ≤ 1/6 + (5/6-δ)*(N/D) := by
  have hN : N = N/D*D := (div_mul_cancel₀ N hD.ne').symm
  have hfac : (5/6 - δ + sI')*N - (5/6 - q + sI'*w)*D =
      ((5/6 - δ + sI')*(N/D) - (5/6 - q + sI'*w))*D := by
    conv_lhs => rw [hN]
    ring
  rw [hfac] at h
  have key := (mul_pos_iff_of_pos_right hD).mp h
  nlinarith

theorem facts_of_region {δ p : ℝ} (h : inRegion δ p) : RegionFacts δ p := by
  have hp := region_mem h
  obtain ⟨hδ, hp⟩ := hp
  have hl := lambda_mem
  have hB := B_mem
  have hD : 0 < tDen δ p := by
    unfold tDen sI sP; rat_pos [hδ, hp, hl, hB]
  have hS : 0 < sI δ p + sP δ p := by
    unfold sI sP; rat_pos [hδ, hp, hl, hB]
  have hDC : 0 < tDenC δ p := by
    unfold tDenC sI sPc; rat_pos [hδ, hp]
  have hSC : 0 < sI δ p + sPc δ := by
    unfold sI sPc; rat_pos [hδ, hp]
  obtain ⟨hi, hpl⟩ := crossing_identities hD.ne' hS.ne'
  obtain ⟨hiC, hplC⟩ := crossing_identitiesC hDC.ne' hSC.ne'
  refine ⟨hD, hS, hDC, hSC, ⟨?_, rfl, rfl, hi, hpl, ?_, ?_, ?_, ?_⟩,
    ⟨?_, rfl, rfl, hiC, hplC, ?_, ?_, ?_, ?_⟩⟩
  · apply le_of_lt; unfold sP; rat_pos [hδ, hp, hl, hB]
  · apply le_of_cleared hD
    unfold cutoffFloor inverseFloor windowBottom crossingSlack tNum tDen sI sP aP
    rat_pos [hδ, hp, hl, hB]
  · apply le_of_cleared' hD
    unfold tNum tDen sI sP aP
    rat_pos [hδ, hp, hl, hB]
  · apply crossing_of_cleared hD hS
    unfold crossingFloor inverseFloor crossingSlack tNum tDen sI sP aP
    rat_pos [hδ, hp, hl, hB]
  · apply window_of_cleared hD
    unfold windowBottom tNum tDen sI sP aP
    rat_pos [hδ, hp, hl, hB]
  · apply le_of_lt; unfold sPc; rat_pos [hδ]
  · apply le_of_cleared hDC
    unfold cutoffFloor inverseFloor windowBottom crossingSlack tNumC tDenC sI sPc aPc Cycle63.Optimization.slotTop
    rat_pos [hδ, hp]
  · apply le_of_cleared' hDC
    unfold tNumC tDenC sI sPc aPc Cycle63.Optimization.slotTop
    rat_pos [hδ, hp]
  · apply crossing_of_cleared hDC hSC
    unfold crossingFloor inverseFloor crossingSlack tNumC tDenC sI sPc aPc Cycle63.Optimization.slotTop
    rat_pos [hδ, hp]
  · apply window_of_cleared hDC
    unfold windowBottom tNumC tDenC sI sPc aPc Cycle63.Optimization.slotTop
    rat_pos [hδ, hp]

/-! Monotonicity in the prime amplitude. The cutoff numerator and denominator are quadratics in
the amplitude; the cross difference of two quotients factors through a symmetric bilinear form,
whose sign on the region follows from its three corner values. -/

theorem quadratic_cross (n0 n1 n2 d0 d1 d2 x y : ℝ) :
    (n0 + n1*y + n2*y^2)*(d0 + d1*x + d2*x^2) - (n0 + n1*x + n2*x^2)*(d0 + d1*y + d2*y^2) =
      (y - x)*((n1*d0 - n0*d1) + (n2*d0 - n0*d2)*(x + y) + (n2*d1 - n1*d2)*(x*y)) := by
  ring

/-- A bilinear form on a square is bounded by its corners. -/
theorem bilinear_corners {A Bc C c e p p' : ℝ} (hce : c < e)
    (hp : p ∈ Set.Icc c e) (hp' : p' ∈ Set.Icc c e)
    (h1 : A + Bc*(c+c) + C*(c*c) ≤ 0) (h2 : A + Bc*(c+e) + C*(c*e) ≤ 0)
    (h3 : A + Bc*(e+e) + C*(e*e) ≤ 0) :
    A + Bc*(p+p') + C*(p*p') ≤ 0 := by
  have hL : 0 < (e-c)^2 := by
    have : 0 < e - c := by linarith
    positivity
  have hid : (e-c)^2*(A + Bc*(p+p') + C*(p*p')) =
      (e-p)*(e-p')*(A + Bc*(c+c) + C*(c*c)) +
        ((p-c)*(e-p') + (e-p)*(p'-c))*(A + Bc*(c+e) + C*(c*e)) +
        (p-c)*(p'-c)*(A + Bc*(e+e) + C*(e*e)) := by ring
  have w1 : 0 ≤ (e-p)*(e-p') := mul_nonneg (by linarith [hp.2]) (by linarith [hp'.2])
  have w2 : 0 ≤ (p-c)*(e-p') + (e-p)*(p'-c) :=
    add_nonneg (mul_nonneg (by linarith [hp.1]) (by linarith [hp'.2]))
      (mul_nonneg (by linarith [hp.2]) (by linarith [hp'.1]))
  have w3 : 0 ≤ (p-c)*(p'-c) := mul_nonneg (by linarith [hp.1]) (by linarith [hp'.1])
  have := mul_nonpos_of_nonneg_of_nonpos w1 h1
  have := mul_nonpos_of_nonneg_of_nonpos w2 h2
  have := mul_nonpos_of_nonneg_of_nonpos w3 h3
  have hneg : (e-c)^2*(A + Bc*(p+p') + C*(p*p')) ≤ 0 := by rw [hid]; linarith
  by_contra hc
  have hc' := not_le.mp hc
  have := mul_pos hL hc'
  linarith

/-- Coefficients of the affine cutoff numerator and denominator as quadratics in the amplitude. -/
def nA0 (δ : ℝ) : ℝ := 5*δ/2
def nA1 (δ : ℝ) : ℝ := -δ*(12*B*δ + 12*δ*lambda + 5*lambda + 20)/(6*lambda)
def nA2 (δ : ℝ) : ℝ := 2*δ^2*(B + 2)/lambda
def dA0 (δ : ℝ) : ℝ := δ*(5 - 2*δ)/2
def dA1 (δ : ℝ) : ℝ := -δ*(6*δ*lambda + 5*lambda + 20)/(6*lambda)
def dA2 (δ : ℝ) : ℝ := 4*δ^2/lambda

theorem tNum_quad (δ p : ℝ) : tNum δ p = nA0 δ + nA1 δ*p + nA2 δ*p^2 := by
  have hl : lambda ≠ 0 := lambda_pos.ne'
  unfold tNum sI sP aP nA0 nA1 nA2
  field_simp
  ring

theorem tDen_quad (δ p : ℝ) : tDen δ p = dA0 δ + dA1 δ*p + dA2 δ*p^2 := by
  have hl : lambda ≠ 0 := lambda_pos.ne'
  unfold tDen sI sP dA0 dA1 dA2
  field_simp
  ring

/-- Coefficients of the capped cutoff numerator and denominator. -/
def nC0 (δ : ℝ) : ℝ := 5*δ/2
def nC1 (δ : ℝ) : ℝ := -δ*((2 + 2*Cycle63.Optimization.slotTop)*δ + 5/6)
def nC2 (δ : ℝ) : ℝ := 2*Cycle63.Optimization.slotTop*δ^2
def dC0 (δ : ℝ) : ℝ := δ*(5 - 2*δ)/2
def dC1 (δ : ℝ) : ℝ := -δ*(6*δ + 5)/6

theorem tNumC_quad (δ p : ℝ) : tNumC δ p = nC0 δ + nC1 δ*p + nC2 δ*p^2 := by
  unfold tNumC sI sPc aPc nC0 nC1 nC2
  ring

theorem tDenC_quad (δ p : ℝ) : tDenC δ p = dC0 δ + dC1 δ*p + 0*p^2 := by
  unfold tDenC sI sPc dC0 dC1
  ring

/-- A quotient of quadratics with positive denominators is nonincreasing on `[c, e]` when the
cross form is nonpositive at the three corners. -/
theorem quotient_anti {n0 n1 n2 d0 d1 d2 c e x y : ℝ} (hce : c < e)
    (hx : x ∈ Set.Icc c e) (hy : y ∈ Set.Icc c e) (hxy : x ≤ y)
    (hDx : 0 < d0 + d1*x + d2*x^2) (hDy : 0 < d0 + d1*y + d2*y^2)
    (h1 : (n1*d0 - n0*d1) + (n2*d0 - n0*d2)*(c+c) + (n2*d1 - n1*d2)*(c*c) ≤ 0)
    (h2 : (n1*d0 - n0*d1) + (n2*d0 - n0*d2)*(c+e) + (n2*d1 - n1*d2)*(c*e) ≤ 0)
    (h3 : (n1*d0 - n0*d1) + (n2*d0 - n0*d2)*(e+e) + (n2*d1 - n1*d2)*(e*e) ≤ 0) :
    (n0 + n1*y + n2*y^2)/(d0 + d1*y + d2*y^2) ≤ (n0 + n1*x + n2*x^2)/(d0 + d1*x + d2*x^2) := by
  rw [div_le_div_iff₀ hDy hDx]
  have hG := bilinear_corners hce hx hy h1 h2 h3
  have hcross := quadratic_cross n0 n1 n2 d0 d1 d2 x y
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hG
  linarith

theorem tStar_anti {δ p p' : ℝ} (h : inRegion δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) :
    tStar δ p' ≤ tStar δ p := by
  have h' := inRegion_up h hpp hp'
  have hD := (facts_of_region h).den
  have hD' := (facts_of_region h').den
  have hδ := (region_mem h).1
  have hl := lambda_mem
  have hB := B_mem
  rw [tDen_quad] at hD hD'
  unfold tStar
  rw [tNum_quad, tDen_quad, tNum_quad, tDen_quad]
  apply quotient_anti (c := 495/1000) (e := 1/2) (by norm_num) (region_mem h).2 (region_mem h').2
    hpp hD hD' <;>
  · apply le_of_lt
    unfold nA0 nA1 nA2 dA0 dA1 dA2
    rat_pos [hδ, hl, hB]

theorem tStarC_anti {δ p p' : ℝ} (h : inRegion δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) :
    tStarC δ p' ≤ tStarC δ p := by
  have h' := inRegion_up h hpp hp'
  have hD := (facts_of_region h).denC
  have hD' := (facts_of_region h').denC
  have hδ := (region_mem h).1
  rw [tDenC_quad] at hD hD'
  unfold tStarC
  rw [tNumC_quad, tDenC_quad, tNumC_quad, tDenC_quad]
  apply quotient_anti (c := 495/1000) (e := 1/2) (by norm_num) (region_mem h).2 (region_mem h').2
    hpp hD hD' <;>
  · apply le_of_lt
    unfold nC0 nC1 nC2 dC0 dC1 Cycle63.Optimization.slotTop
    rat_pos [hδ]

/-- The closed form is nonincreasing in the prime amplitude on the region. -/
theorem RStar_anti {δ p p' : ℝ} (h : inRegion δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) :
    RStar δ p' ≤ RStar δ p := by
  have ht := tStar_anti h hpp hp'
  have hv : 0 ≤ 5/6-δ := by linarith [h.2.1]
  unfold RStar
  nlinarith

theorem RStarC_anti {δ p p' : ℝ} (h : inRegion δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) :
    RStarC δ p' ≤ RStarC δ p := by
  have ht := tStarC_anti h hpp hp'
  have hv : 0 ≤ 5/6-δ := by linarith [h.2.1]
  unfold RStarC
  nlinarith

end
end Cycle63.CountAffine

end Record1252270103Bootstrap.PR67
