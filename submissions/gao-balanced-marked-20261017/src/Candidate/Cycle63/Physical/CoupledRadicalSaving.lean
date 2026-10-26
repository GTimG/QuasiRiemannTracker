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

theorem first_common_uniform (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 103/273) (hδ : 17/25 ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤ -(519/4550)*c-E := by
  have hh := first_common_coupled ρ δ c d p R E Lc R₀
    hρ (by linarith) hp hpC hpD hRp hR₀ hLc
  have hh' := mul_nonneg (show 0 ≤ δ-3*ρ/2-519/4550 by linarith)
    (show 0 ≤ c by linarith)
  nlinarith

end
end CoupledRadicalSaving

#print axioms CoupledRadicalSaving.first_common_coupled
#print axioms CoupledRadicalSaving.first_common_uniform
