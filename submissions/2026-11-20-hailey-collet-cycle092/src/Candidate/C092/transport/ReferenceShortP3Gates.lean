/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform literal scale gates for the original annular P.3 reference. -/
import Candidate.C092.transport.ReferenceShortP3Geometry

set_option autoImplicit false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped BigOperators
open Filter

theorem original_fourth_volume_le {ι : Type} [Fintype ι]
    (w : ι→ℝ) {U X b W : ℝ} (hU : 1 ≤ U) (hX : 0 ≤ X)
    (hshort : X ≤ U^b) (hslots : (∑ i,w i) ≤ W) :
    X^2*(∏ i,U^(w i))^2 ≤ U^(2*(b+W)) := by
  have hu : 0 < U := zero_lt_one.trans_le hU
  have hp : (∏ i,U^(w i)) ≤ U^W := by
    rw [←Real.rpow_sum_of_pos hu]
    exact Real.rpow_le_rpow_of_exponent_le hU hslots
  have hn : 0 ≤ ∏ i,U^(w i) := Finset.prod_nonneg (fun i _ => (Real.rpow_pos_of_pos hu _).le)
  calc
    _ ≤ (U^b)^2*(U^W)^2 := mul_le_mul (pow_le_pow_left₀ hX hshort 2)
      (pow_le_pow_left₀ hn hp 2) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by
      rw [←mul_pow,←Real.rpow_add hu,←Real.rpow_natCast,←Real.rpow_mul hu.le]
      congr 1
      ring

theorem uniform_original_short_gates {H W ξ : ℝ} (hH : H ≤ 1) (hξ : 0 ≤ ξ)
    (hreserve : 4*(shortWidth+W)+ξ/2 < H) :
    ∀ᶠ U : ℝ in atTop, 1 ≤ U ∧
      ∀ {ι : Type} [Fintype ι] (w : ι→ℝ) (X : ℝ),
      0 ≤ X → X ≤ U^shortWidth → (∑ i,w i) ≤ W →
      X^2*(∏ i,U^(w i))^2 ≤ U^(2:ℝ) ∧
      4*((X^2*(∏ i,U^(w i))^2)^2/(U^H))*U^(ξ/2) < 1 := by
  filter_upwards [eventually_short_cutoff hreserve] with U hU
  refine ⟨hU.1,?_⟩
  intro ι _ w X hX hshort hslots
  have hv := original_fourth_volume_le w hU.1 hX hshort hslots
  have hwidth : 2*(shortWidth+W) ≤ 2 := by linarith
  refine ⟨hv.trans (Real.rpow_le_rpow_of_exponent_le hU.1 hwidth),?_⟩
  exact short_cutoff_of_power hU.1 (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hv rfl hU.2

#print axioms original_fourth_volume_le
#print axioms uniform_original_short_gates
end
end QRH.Cycle092.ReferenceShortP3
