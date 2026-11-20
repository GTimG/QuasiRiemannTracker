/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete P15 mass remains LINEAR after the actual second-Cauchy step. -/
import Candidate.C092.transport.MixedPacketWitnessKernel

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators

/-- Normalize by the complete coefficient mass before Cauchy, so favorable
prime damping cannot be lost by promoting Mass^2 to a constant at least one. -/
theorem packet_second_cauchy {Row : Type} (rows : Finset Row)
    (packet ordinary selected full reciprocal : Row→ℂ)
    (U R G total inverse ordinaryLower selectedLower epsilon Ccount Cmoment Mass : ℝ)
    (hU : 0<U) (hc : 1≤Ccount) (hm : 1≤Cmoment) (hMass : 0<Mass)
    (hcard : (rows.card:ℝ)≤Ccount*U^(R-G))
    (hordinary : ∀u∈rows,U^ordinaryLower≤‖ordinary u‖^2)
    (hselected : ∀u∈rows,U^selectedLower≤‖selected u‖)
    (hfull : ∀u∈rows,‖full u‖≤U^total)
    (hinverse : ∀u∈rows,‖reciprocal u‖≤U^inverse)
    (henergy : (∑u∈rows,‖packet u*ordinary u*selected u‖^2)≤Mass^2*Cmoment*U^(1+epsilon)) :
    (∑u∈rows,‖packet u*full u*reciprocal u‖)≤Mass*Ccount*Cmoment*
      U^(total+inverse-selectedLower-ordinaryLower/2+(R+1+epsilon)/2-G/2) := by
  let P (u : Row) := packet u/(Mass:ℂ)
  have henergy' : (∑u∈rows,‖P u*ordinary u*selected u‖^2)≤Cmoment*U^(1+epsilon) := by
    have heq : Mass^2*(∑u∈rows,‖P u*ordinary u*selected u‖^2) =
        ∑u∈rows,‖packet u*ordinary u*selected u‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      dsimp [P]
      simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hMass.le,mul_pow,div_pow]
      field_simp
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hMass)).mp
    exact heq.le.trans (henergy.trans_eq (by ring))
  have hh := MixedPacketWitness.saturated_second_bin rows P ordinary selected full reciprocal
    U R G total inverse ordinaryLower selectedLower epsilon Ccount Cmoment hU hc hm
    hcard hordinary hselected hfull hinverse henergy'
  have heq : (∑u∈rows,‖packet u*full u*reciprocal u‖) =
      Mass*(∑u∈rows,‖P u*full u*reciprocal u‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    dsimp [P]
    simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hMass.le]
    field_simp
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hh hMass.le).trans_eq (by ring)

#print axioms packet_second_cauchy
end
end QRH.Cycle092.MixedMiddleReturn
