import Candidate.Cycle62.Physical.InitialMass.GeometryBudgetContraction

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section

/-- At large outer heights, a fixed polynomial height factor absorbs any
fixed coarse power of the scale. The degree precedes the scale and height. -/
theorem geometry_large_height_absorption (coarse target τ : ℝ)(hτ : 0<τ) :
    ∃n : ℕ,∀Z H : ℝ,1≤Z → Z^τ≤H → Z^coarse≤Z^target*H^n := by
  obtain ⟨n,hn⟩:=exists_nat_gt ((coarse-target)/τ)
  refine ⟨n,?_⟩
  intro Z H hZ hH
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hn' : coarse≤target+τ*(n:ℝ) := by
    have hh:=(div_lt_iff₀ hτ).mp hn
    linarith
  calc
    Z^coarse≤Z^(target+τ*(n:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _=Z^target*(Z^τ)^n := by rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_natCast]
    _≤Z^target*H^n := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) hH n) (Real.rpow_nonneg hz.le _)

/-- Combine a truncated analytic estimate with an all-height coarse one.
The coarse estimate is used only beyond the proved analytic height range. -/
theorem geometry_extend_height_bound (coarse target τ : ℝ)(hτ : 0<τ)(smallDegree : ℕ) :
    ∃degree : ℕ,∀Z H E Csmall Ccoarse control : ℝ,
      1≤Z → 1≤H → 0≤Csmall → 0≤Ccoarse → 0≤control →
      (H≤Z^τ → E≤Csmall*control*Z^target*H^smallDegree) →
      E≤Ccoarse*control*Z^coarse →
      E≤(Csmall+Ccoarse)*control*Z^target*H^degree := by
  obtain ⟨n,hn⟩:=geometry_large_height_absorption coarse target τ hτ
  refine ⟨max n smallDegree,?_⟩
  intro Z H E Cs Cc control hZ hH hCs hCc hc hsmall hcoarse
  have hz : 0≤Z := zero_le_one.trans hZ
  by_cases h : H≤Z^τ
  · apply (hsmall h).trans
    apply mul_le_mul
    · gcongr; linarith
    · exact pow_le_pow_right₀ hH (le_max_right _ _)
    · positivity
    · positivity
  · have hh:=hn Z H hZ (le_of_lt (lt_of_not_ge h))
    calc
      E≤Cc*control*Z^coarse := hcoarse
      _≤Cc*control*(Z^target*H^n) := mul_le_mul_of_nonneg_left hh (mul_nonneg hCc hc)
      _≤(Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
        rw [←mul_assoc]
        apply mul_le_mul
        · gcongr; linarith
        · exact pow_le_pow_right₀ hH (le_max_left _ _)
        · positivity
        · positivity

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_large_height_absorption
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_extend_height_bound
