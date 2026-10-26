import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
Scalar consequences of the exact directional common-prime valuation facets.

UNIMPLEMENTED HERE: transporting the actual ideal numerators to the hypotheses
`hdir`.  The proposed left/right ideal divisibilities are respectively
  numerator * activeRadical^2 * cancelledRadical^3 | C * D^2
and
  numerator * activeRadical^2 * cancelledRadical^3 | C^2 * D.
This file proves no new physical source theorem or fixed-strip endpoint.
-/

namespace ValuationGain
noncomputable section

def firstCommon (ρ δ c d R E Lc R₀ : ℝ) : ℝ :=
  (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
    max (3*c-5*d-R) 0/6+ρ*Lc+R₀

/-- On the `c ≥ d` branch either actual signed orientation has the same safe
rate.  The second directional facet is the extremal one on this branch. -/
theorem first_common_directional_hi (ρ δ c d R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5) (hcd : d ≤ c)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hdir : Lc ≤ c+2*d-2*R-3*R₀ ∨ Lc ≤ 2*c+d-2*R-3*R₀) :
    firstCommon ρ δ c d R E Lc R₀ ≤
      -(δ-(4+35*ρ)/36)*c-E := by
  have hnew : Lc ≤ 2*c+d-2*R-3*R₀ := by
    rcases hdir with hleft | hright
    · linarith
    · exact hright
  have hfac := mul_le_mul_of_nonneg_left hnew
    (show 0 ≤ 19*ρ-4 by linarith)
  have hcoarse := mul_le_mul_of_nonneg_left hLc
    (show 0 ≤ 17*ρ+4 by linarith)
  have hpen := mul_le_mul_of_nonneg_left
    (le_max_left (3*c-5*d-R) 0) (show 0 ≤ 8-11*ρ by linarith)
  have hpenExtra := mul_nonneg (show 0 ≤ 11*ρ-2 by linarith)
    (le_max_right (3*c-5*d-R) 0)
  have hcancel := mul_nonneg (show 0 ≤ 142*ρ-28 by linarith) hR₀
  unfold firstCommon
  rw [max_eq_left (sub_nonneg.mpr hcd)]
  nlinarith

/-- Exact scalar common-part improvement, keeping the natural inactive
projector loss `E`, the positive-part penalty, and cancelled radical `R₀`.
The piecewise rate is necessary: `δ+1-4ρ` alone fails near `δ=7/10`. -/
theorem first_common_exact (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hdir : Lc ≤ c+2*d-2*R-3*R₀ ∨ Lc ≤ 2*c+d-2*R-3*R₀) :
    firstCommon ρ δ c d R E Lc R₀ ≤
      -(δ-max (4*ρ-1) ((4+35*ρ)/36))*c-E := by
  have hc : 0 ≤ c := hp.trans hpC
  by_cases hcd : d ≤ c
  · have hh := first_common_directional_hi ρ δ c d R E Lc R₀
      hρ hρmax hcd hR₀ hLc hdir
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_right (4*ρ-1) ((4+35*ρ)/36)) hc
    nlinarith
  · have hnum := mul_le_mul_of_nonneg_left hLc (show 0 ≤ ρ by linarith)
    have hrad := mul_le_mul_of_nonneg_left (hRp.trans hpC)
      (show 0 ≤ 4*ρ-1 by linarith)
    have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
    have hpen := le_max_right (3*c-5*d-R) 0
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_left (4*ρ-1) ((4+35*ρ)/36)) hc
    unfold firstCommon
    rw [max_eq_right (show c-d ≤ 0 by linarith)]
    nlinarith

/-- Uniform scalar rate over the proposed `q = 27/40` source interval. -/
theorem first_common_uniform_27_40 (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 28/73) (hδ : 27/40 ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hdir : Lc ≤ c+2*d-2*R-3*R₀ ∨ Lc ≤ 2*c+d-2*R-3*R₀) :
    firstCommon ρ δ c d R E Lc R₀ ≤ -(411/2920)*c-E := by
  have hh := first_common_exact ρ δ c d p R E Lc R₀ hρ (by linarith)
    hp hpC hpD hRp hR₀ hLc hdir
  have hmax : max (4*ρ-1) ((4+35*ρ)/36) ≤ 39/73 := by
    apply max_le <;> linarith
  have hgap := mul_nonneg
    (show 0 ≤ δ-max (4*ρ-1) ((4+35*ρ)/36)-411/2920 by linarith)
    (hp.trans hpC)
  nlinarith

/-- The symmetric norm facet combines with the cancelled-radical bound before
either signed orientation is discarded. -/
theorem symmetric_radical_facet (ρ c d R Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hnorm : 4*Lc ≤ 5*(c+d)) :
    21*ρ*Lc+21*R₀ ≤ (19*ρ-4)*(c+d)+(16+29*ρ)*R := by
  have hnorm' := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ 19*ρ-4 by linarith)
  have hrad := mul_le_mul_of_nonneg_left hLc
    (show 0 ≤ 16+29*ρ by linarith)
  have hcancel := mul_nonneg (show 0 ≤ 29*ρ-5 by linarith) hR₀
  nlinarith

theorem first_common_symmetric_hi (ρ δ c d R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5) (hcd : d ≤ c)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hnorm : 4*Lc ≤ 5*(c+d)) :
    firstCommon ρ δ c d R E Lc R₀ ≤ -(δ-(2+22*ρ)/21)*c-E := by
  have hfacet := symmetric_radical_facet ρ c d R Lc R₀ hρ hR₀ hLc hnorm
  have hpen := mul_le_mul_of_nonneg_left
    (le_max_left (3*c-5*d-R) 0) (show 0 ≤ 5-8*ρ by linarith)
  have hpenExtra := mul_nonneg (show 0 ≤ 16*ρ-3 by linarith)
    (le_max_right (3*c-5*d-R) 0)
  unfold firstCommon
  rw [max_eq_left (sub_nonneg.mpr hcd)]
  nlinarith

/-- Source-consumable scalar improvement: unlike `first_common_exact`, this
requires only the symmetric norm facet proved for the actual numerator in
`FirstNumeratorValuation.lean`, with no directional transport assumption. -/
theorem first_common_symmetric (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (_hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hnorm : 4*Lc ≤ 5*(c+d)) :
    firstCommon ρ δ c d R E Lc R₀ ≤
      -(δ-max (4*ρ-1) ((2+22*ρ)/21))*c-E := by
  have hc : 0 ≤ c := hp.trans hpC
  by_cases hcd : d ≤ c
  · have hh := first_common_symmetric_hi ρ δ c d R E Lc R₀
      hρ hρmax hcd hR₀ hLc hnorm
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_right (4*ρ-1) ((2+22*ρ)/21)) hc
    nlinarith
  · have hnum := mul_le_mul_of_nonneg_left hLc (show 0 ≤ ρ by linarith)
    have hrad := mul_le_mul_of_nonneg_left (hRp.trans hpC)
      (show 0 ≤ 4*ρ-1 by linarith)
    have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
    have hpen := le_max_right (3*c-5*d-R) 0
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_left (4*ρ-1) ((2+22*ρ)/21)) hc
    unfold firstCommon
    rw [max_eq_right (show c-d ≤ 0 by linarith)]
    nlinarith

theorem first_common_symmetric_uniform_27_40 (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 28/73) (hδ : 27/40 ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hnorm : 4*Lc ≤ 5*(c+d)) :
    firstCommon ρ δ c d R E Lc R₀ ≤ -(411/2920)*c-E := by
  have hh := first_common_symmetric ρ δ c d p R E Lc R₀ hρ (by linarith)
    hp hpC hpD hRp hR₀ hLc hnorm
  have hmax : max (4*ρ-1) ((2+22*ρ)/21) ≤ 39/73 := by
    apply max_le <;> linarith
  have hgap := mul_nonneg
    (show 0 ≤ δ-max (4*ρ-1) ((2+22*ρ)/21)-411/2920 by linarith)
    (hp.trans hpC)
  nlinarith

/-- A literal feasible mixture disproves the unqualified `δ+1-4ρ` rate.
The right signed types `(1,5)` and `(3,1)` realize these normalized totals. -/
theorem gamma_only_counterexample :
    firstCommon (19/54) (7/10) 1 (19/36) (13/36) 0 (65/36) 0 +
      (7/10+1-4*(19/54)) = 89/1944 := by
  norm_num [firstCommon]

end
end ValuationGain

#print axioms ValuationGain.first_common_directional_hi
#print axioms ValuationGain.first_common_exact
#print axioms ValuationGain.first_common_uniform_27_40
#print axioms ValuationGain.symmetric_radical_facet
#print axioms ValuationGain.first_common_symmetric
#print axioms ValuationGain.first_common_symmetric_uniform_27_40
#print axioms ValuationGain.gamma_only_counterexample
