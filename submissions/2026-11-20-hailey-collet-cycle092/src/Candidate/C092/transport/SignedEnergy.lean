/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Manuscript P.1 (P4), on the original row at its actual supported zero. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness

set_option autoImplicit false
namespace QRH.Cycle092.SignedEnergy
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
variable {Label : Type*} {χ : Label → Character} {U V a ε t T allowance : ℝ} {i : ℕ}

/-- The actual plain polynomial retains the chosen character, profile, length,
real part of the witness zero, and its signed frequency. -/
def actualPlain (w : SupportedWitness χ (U^V) a ε t T allowance i) : ℂ :=
  polynomial (χ w.label) false positiveAnnular ((U^V)^w.m) w.zero.re
    (2*Real.pi*w.nu-w.zero.im)

def oriented (reverse : Bool) (s : ℂ) : ℂ := if reverse then star s else s

@[simp] theorem norm_oriented (reverse : Bool) (s : ℂ) : ‖oriented reverse s‖ = ‖s‖ := by
  cases reverse <;> simp [oriented]

/-- No cancellation of a possibly zero divisor. This accounts explicitly for
both the original length's upper loss and the `2ε` in the actual witness. -/
theorem actual_same_zero (hU : 0 < U) (w : SupportedWitness χ (U^V) a ε t T allowance i)
    (A_y A_n Q : ℂ) (reverse : Bool) {y δ : ℝ}
    (hy : ‖A_y‖^2 ≤ U^((2*a-1)*y+δ)) :
    ‖A_n*A_y*Q‖^2 ≤ U^((2*a-1)*(y-V*w.m)+δ+2*V*ε) *
      ‖A_n*(oriented reverse (actualPlain w))*Q‖^2 := by
  let f := (2*a-1)*(y-V*w.m)+δ+2*V*ε
  have hw : U^(V*((2*a-1)*w.m-2*ε)) ≤ ‖actualPlain w‖^2 := by
    rw [Real.rpow_mul hU.le]; exact w.plain_spike
  have hn : U^f * U^(V*((2*a-1)*w.m-2*ε)) ≤ U^f * ‖actualPlain w‖^2 :=
    mul_le_mul_of_nonneg_left hw (Real.rpow_pos_of_pos hU _).le
  rw [←Real.rpow_add hU, show f+V*((2*a-1)*w.m-2*ε)=(2*a-1)*y+δ by dsimp [f];ring] at hn
  simp only [norm_mul, mul_pow, norm_oriented]
  calc
    _ ≤ ‖A_n‖^2 * (U^f * ‖actualPlain w‖^2) * ‖Q‖^2 := by gcongr; exact hy.trans hn
    _ = _ := by dsimp [f]; ring

/-- Apply P4 to an arbitrary finite selected subclass. Each index retains its
own zero, character family, mark, orientation, and profile; nonnegative weights
can contain arbitrary masks. The cutoff is allowed its exact witness loss. -/
theorem actual_row_energy {Row : Type*} (s : Finset Row) (fam : Row → Label → Character)
    (ws : ∀ u, SupportedWitness (fam u) (U^V) a ε t T allowance i)
    (wgt : Row → ℝ) (A_y A_n Q : Row → ℂ) (rev : Row → Bool) {y δ m₀ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hν : 0 ≤ 2*a-1)
    (hwgt : ∀ u∈s, 0 ≤ wgt u) (hy : ∀ u∈s, ‖A_y u‖^2 ≤ U^((2*a-1)*y+δ))
    (hcut : ∀ u∈s, (ws u).r ≤ t-m₀) :
    ∑ u∈s, wgt u*‖A_n u*A_y u*Q u‖^2 ≤
      U^((2*a-1)*(y-V*(m₀-ε))+δ+2*V*ε) *
        ∑ u∈s, wgt u*‖A_n u*oriented (rev u) (actualPlain (ws u))*Q u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hm : m₀-ε ≤ (ws u).m := by linarith [(ws u).product_length_lower, hcut u hu]
  have hex : (2*a-1)*(y-V*(ws u).m)+δ+2*V*ε ≤ (2*a-1)*(y-V*(m₀-ε))+δ+2*V*ε := by gcongr
  have hz := (actual_same_zero (zero_lt_one.trans_le hU) (ws u) (A_y u) (A_n u) (Q u) (rev u) (hy u hu)).trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hU hex) (sq_nonneg _))
  exact (mul_le_mul_of_nonneg_left hz (hwgt u hu)).trans_eq (by ring)

#print axioms actual_same_zero
#print axioms actual_row_energy
end
end QRH.Cycle092.SignedEnergy
