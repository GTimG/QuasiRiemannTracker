/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact matching of the actual P4 right sum to the proved witness-source sum. -/
import Candidate.C092.transport.WitnessRowSupActualRegular

set_option autoImplicit false
namespace QRH.Cycle092.WitnessRowSup.Actual
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness
open QRH.Cycle092.SignedEnergy

/-- P4's orientation conjugates the entire witness value. Its norm in the
original weighted product is exactly the actual_witness_rowwise product. -/
theorem P4_right_energy {Row Label : Type*} [Fintype Row]
    (χ : Row→Label→Character) {U d a ε cutoff T allowance : ℝ} {i : ℕ}
    (ws : ∀ u,SupportedWitness (χ u) (U^d) a ε cutoff T allowance i)
    (weight : Row→ℝ) (A_n Q : Row→ℂ) (reverse : Row→Bool) :
    (∑ u,weight u*‖A_n u*oriented (reverse u) (actualPlain (ws u))*Q u‖^2) =
      ∑ u,weight u*‖actualPlain (ws u)*(A_n u*Q u)‖^2 := by
  apply Finset.sum_congr rfl
  intro u _
  simp only [norm_mul,norm_oriented,mul_pow]
  ring

/-- Composing the actual regular_core_P4 inequality with the proved source
sum requires only a nonnegative outer P4 coefficient. In use `hsource` is the
whole-family conclusion of actual_witness_rowwise, never a per-row profile
estimate. This equation retains P4's original weight and product ordering. -/
theorem P4_finish {Row Label : Type*} [Fintype Row]
    (χ : Row→Label→Character) {U d a ε cutoff T allowance : ℝ} {i : ℕ}
    (ws : ∀ u,SupportedWitness (χ u) (U^d) a ε cutoff T allowance i)
    (weight : Row→ℝ) (A_n A_y Q : Row→ℂ) (reverse : Row→Bool)
    (price bound : ℝ) (hprice : 0 ≤ price)
    (hP4 : (∑ u,weight u*‖A_n u*A_y u*Q u‖^2) ≤
      price*∑ u,weight u*‖A_n u*oriented (reverse u) (actualPlain (ws u))*Q u‖^2)
    (hsource : (∑ u,weight u*‖actualPlain (ws u)*(A_n u*Q u)‖^2) ≤ bound) :
    (∑ u,weight u*‖A_n u*A_y u*Q u‖^2) ≤ price*bound := by
  rw [P4_right_energy χ ws weight A_n Q reverse] at hP4
  exact hP4.trans (mul_le_mul_of_nonneg_left hsource hprice)

#print axioms P4_right_energy
#print axioms P4_finish
end
end QRH.Cycle092.WitnessRowSup.Actual
