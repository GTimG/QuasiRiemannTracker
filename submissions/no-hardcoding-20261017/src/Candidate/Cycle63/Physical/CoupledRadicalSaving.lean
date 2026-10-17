import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CoupledRadicalSaving
noncomputable section

/-- Retaining the radical penalty prevents an unbalanced common allocation
from exhausting the source width at the weak unmarked rate. -/
theorem first_common_coupled (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤ -(δ-3*ρ/2)*c-E := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hc : 0 ≤ c := by linarith
  have hRc : R ≤ c := hRp.trans hpC
  have hRd : R ≤ d := hRp.trans hpD
  have hnum := mul_le_mul_of_nonneg_left hLc hρ0
  have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
  have hpen0 : 0 ≤ max (3*c-5*d-R) 0 := le_max_right _ _
  have hpen : 3*c-5*d-R ≤ max (3*c-5*d-R) 0 := le_max_left _ _
  by_cases hcd : d ≤ c
  · rw [max_eq_left (sub_nonneg.mpr hcd)]
    have hrad := mul_le_mul_of_nonneg_left hRd (show 0 ≤ 4*ρ-1 by linarith)
    by_cases hd : d ≤ c/2
    · have hbalance := mul_le_mul_of_nonneg_left hd (show 0 ≤ 5*ρ-1 by linarith)
      nlinarith
    · have hbalance := mul_le_mul_of_nonneg_left (show c/2 ≤ d by linarith)
        (show 0 ≤ 2-5*ρ by linarith)
      nlinarith
  · rw [max_eq_right (show c-d ≤ 0 by linarith)]
    have hrad := mul_le_mul_of_nonneg_left hRc (show 0 ≤ 4*ρ-1 by linarith)
    have hbalance := mul_nonneg (show 0 ≤ 1-5*ρ/2 by linarith) hc
    nlinarith

/-- The coupled saving is uniform over the zero bins `δ ≥ q`: its coefficient is at least
`q - 3 ρ₀/2` when the density is at most `ρ₀`. -/
theorem first_common_uniform (q ρ₀ ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ ρ₀) (hρ₀ : ρ₀ ≤ 2/5) (hδ : q ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤ -(q-3*ρ₀/2)*c-E := by
  have hh := first_common_coupled ρ δ c d p R E Lc R₀
    hρ (by linarith) hp hpC hpD hRp hR₀ hLc
  have hh' := mul_nonneg (show 0 ≤ (δ-3*ρ/2)-(q-3*ρ₀/2) by linarith)
    (show 0 ≤ c by linarith)
  nlinarith

/-! With the valuation budget `4 Lc ≤ 5 (c + d)` of the first source numerator the saving rate is
`δ - max (4ρ - 1) ((2 + 22ρ)/21)` (tracker PR #62, Zhongpai Gao, `ScalarValuation.lean`). -/

/-- The symmetric norm facet combines with the cancelled-radical bound. -/
theorem symmetric_radical_facet (ρ c d R Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hnorm : 4*Lc ≤ 5*(c+d)) :
    21*ρ*Lc+21*R₀ ≤ (19*ρ-4)*(c+d)+(16+29*ρ)*R := by
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 19*ρ-4 by linarith)
  have hrad := mul_le_mul_of_nonneg_left hLc (show 0 ≤ 16+29*ρ by linarith)
  have hcancel := mul_nonneg (show 0 ≤ 29*ρ-5 by linarith) hR₀
  nlinarith

theorem first_common_symmetric_hi (ρ δ c d R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5) (hcd : d ≤ c)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) (hnorm : 4*Lc ≤ 5*(c+d)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤ -(δ-(2+22*ρ)/21)*c-E := by
  have hfacet := symmetric_radical_facet ρ c d R Lc R₀ hρ hR₀ hLc hnorm
  have hpen := mul_le_mul_of_nonneg_left (le_max_left (3*c-5*d-R) 0) (show 0 ≤ 5-8*ρ by linarith)
  have hpenExtra := mul_nonneg (show 0 ≤ 16*ρ-3 by linarith) (le_max_right (3*c-5*d-R) 0)
  rw [max_eq_left (sub_nonneg.mpr hcd)]
  nlinarith

/-- The saving rate with the valuation budget, at the bin's own density. -/
theorem first_common_symmetric (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) (hnorm : 4*Lc ≤ 5*(c+d)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤
      -(δ-max (4*ρ-1) ((2+22*ρ)/21))*c-E := by
  have hc : 0 ≤ c := hp.trans hpC
  by_cases hcd : d ≤ c
  · have hh := first_common_symmetric_hi ρ δ c d R E Lc R₀ hρ hρmax hcd hR₀ hLc hnorm
    have hmax := mul_le_mul_of_nonneg_right (le_max_right (4*ρ-1) ((2+22*ρ)/21)) hc
    nlinarith
  · have hnum := mul_le_mul_of_nonneg_left hLc (show 0 ≤ ρ by linarith)
    have hrad := mul_le_mul_of_nonneg_left (hRp.trans hpC) (show 0 ≤ 4*ρ-1 by linarith)
    have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
    have hpen := le_max_right (3*c-5*d-R) 0
    have hmax := mul_le_mul_of_nonneg_right (le_max_left (4*ρ-1) ((2+22*ρ)/21)) hc
    rw [max_eq_right (show c-d ≤ 0 by linarith)]
    nlinarith

/-- The valuation saving is uniform over the bins `δ ≥ q` with density at most `ρ₀`: its rate is
at least `q - max (4ρ₀ - 1) ((2 + 22ρ₀)/21)`. -/
theorem first_common_valuation_uniform (q ρ₀ ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ ρ₀) (hρ₀ : ρ₀ ≤ 2/5) (hδ : q ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) (hnorm : 4*Lc ≤ 5*(c+d)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤
      -(q-max (4*ρ₀-1) ((2+22*ρ₀)/21))*c-E := by
  have hh := first_common_symmetric ρ δ c d p R E Lc R₀ hρ (by linarith) hp hpC hRp hR₀ hLc hnorm
  have hm : max (4*ρ-1) ((2+22*ρ)/21) ≤ max (4*ρ₀-1) ((2+22*ρ₀)/21) :=
    max_le_max (by linarith) (by linarith)
  have hc : 0 ≤ c := hp.trans hpC
  have hgap := mul_nonneg (show 0 ≤ (δ-max (4*ρ-1) ((2+22*ρ)/21)) -
    (q-max (4*ρ₀-1) ((2+22*ρ₀)/21)) by linarith) hc
  nlinarith

end
end CoupledRadicalSaving

#print axioms CoupledRadicalSaving.first_common_coupled
#print axioms CoupledRadicalSaving.first_common_uniform
