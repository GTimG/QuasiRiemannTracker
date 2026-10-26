import Candidate.Cycle63.Physical.InitialMass.GeometryHeightAbsorption

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The original height and both Mellin shifts admit separate polynomial
weights. This lets an all-height coarse bound cover the complement of the
analytic range without restricting either integration variable. -/
theorem geometry_shifted_height_product (v height t u : ℝ) (hh : 0≤height) :
    2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤
      (2+4*Real.pi)*(1+|v|+height)*(1+|t|)*(1+|u|) := by
  have hp : 0≤Real.pi := Real.pi_pos.le
  have hv := abs_nonneg v
  have ht := abs_nonneg t
  have hu := abs_nonneg u
  have htu : 0≤|t| * |u| := mul_nonneg ht hu
  have hsum : |t|+|u|≤(1+|t|)*(1+|u|) := by nlinarith
  have hbase : 1+|v|+height≤(1+|v|+height)*(1+|t|)*(1+|u|) := by
    nlinarith [mul_nonneg (add_nonneg hv hh) ht,
      mul_nonneg (add_nonneg hv hh) hu,
      mul_nonneg (add_nonneg hv hh) htu]
  have hshifts : |t|+|u|≤(1+|v|+height)*(1+|t|)*(1+|u|) := by
    nlinarith [mul_nonneg (add_nonneg hv hh) (by positivity : 0≤(1+|t|)*(1+|u|))]
  nlinarith

theorem geometry_extend_shifted_height_bound (coarse target τ : ℝ)
    (hτ : 0<τ) (smallDegree : ℕ) :
    ∃degree : ℕ,∀Z v height t u E Cs Cc control : ℝ,
      1≤Z → 0≤height → 0≤Cs → 0≤Cc → 0≤ control →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤Z^τ →
        E≤Cs*control*Z^target*
          (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree) →
      E≤Cc*control*Z^coarse →
      E≤(2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target*
        (1+|v|+height)^degree*(1+|t|)^degree*(1+|u|)^degree := by
  obtain ⟨degree,hext⟩ := geometry_extend_height_bound coarse target τ hτ smallDegree
  refine ⟨degree,?_⟩
  intro Z v height t u E Cs Cc control hZ hh hCs hCc hc hs hb
  have hH : 1≤2*(1+|v|+height+2*Real.pi*(|t|+|u|)) := by
    have hp : 0≤2*Real.pi*(|t|+|u|) := by positivity
    linarith [abs_nonneg v]
  have h := hext Z _ E Cs Cc control hZ hH hCs hCc hc hs hb
  apply h.trans
  have hp := pow_le_pow_left₀ (by positivity : 0≤2*(1+|v|+height+2*Real.pi*(|t|+|u|)))
    (geometry_shifted_height_product v height t u hh) degree
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : 0≤(Cs+Cc)*control*Z^target)
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hm

end
end OAI.SevenEighths.Cycle63InitialMass
