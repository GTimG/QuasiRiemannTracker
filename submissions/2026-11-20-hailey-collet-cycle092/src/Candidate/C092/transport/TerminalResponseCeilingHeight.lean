/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Scalar height gates for the authentic prime upper supplier. -/
import Candidate.C092.transport.TerminalResponseCeilingFamily

set_option autoImplicit false
namespace QRH.Cycle092.TerminalResponseCeiling
noncomputable section
open Filter

/-- After the finite height bank is fixed, the native polynomial-height
gate holds uniformly as soon as its positive conductor reserve is retained. -/
theorem eventual_native_height_gate (I : ℕ) {τ d η : ℝ}
    (hτ : 0 ≤ τ) (hreserve : 2*τ < d*η) :
    ∀ᶠ U : ℝ in atTop, 1 < U ∧ ∀ i : ℕ, i ≤ I →
      (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η := by
  let C : ℝ := 3+(3*I+2 : ℕ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < d*η-2*τ := sub_pos.mpr hreserve
  have htail := (tendsto_rpow_atTop hgap).eventually (eventually_ge_atTop (C^2))
  filter_upwards [htail,eventually_gt_atTop (1:ℝ)] with U htail hU
  have hUp : 0 < U := zero_lt_one.trans hU
  have hUτ : 1 ≤ U^τ := Real.one_le_rpow hU.le hτ
  have hpow : (U^τ)^2 = U^(2*τ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  refine ⟨hU,?_⟩
  intro i hi
  have hbi : (3*i+2 : ℝ) ≤ (3*I+2 : ℝ) := by exact_mod_cast (show 3*i+2 ≤ 3*I+2 by omega)
  have hb : 3+(3*i+2 : ℕ)*U^τ ≤ C*U^τ := by
    have hh := mul_le_mul_of_nonneg_right hbi (zero_le_one.trans hUτ)
    push_cast at hh ⊢
    dsimp [C]
    push_cast
    nlinarith
  have hleft : 0 ≤ 3+(3*i+2 : ℕ)*U^τ := by positivity
  calc
    _ ≤ (C*U^τ)^2 := pow_le_pow_left₀ hleft hb 2
    _ = C^2*U^(2*τ) := by rw [mul_pow,hpow]
    _ ≤ U^(d*η-2*τ)*U^(2*τ) :=
      mul_le_mul_of_nonneg_right htail (Real.rpow_nonneg hUp.le _)
    _ = (U^d)^η := by
      rw [←Real.rpow_add hUp,←Real.rpow_mul hUp.le]
      congr 1
      ring

/-- Genuine bounded live pitches give the native frequency envelope. -/
theorem native_frequency_gate {U τ t v height : ℝ} (i : ℕ)
    (hU : 0 ≤ U) (hv : |v| ≤ height) (ht : |t|+height ≤ U^τ) :
    |t+v|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ := by
  have hp : 0 ≤ U^τ := Real.rpow_nonneg hU _
  have hi : (2:ℝ) ≤ (3*i+2 : ℕ) := by exact_mod_cast (show 2 ≤ 3*i+2 by omega)
  nlinarith [abs_add_le t v,mul_nonneg (sub_nonneg.mpr hi) hp]

#print axioms eventual_native_height_gate
#print axioms native_frequency_gate
end
end QRH.Cycle092.TerminalResponseCeiling
