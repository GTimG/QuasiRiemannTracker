/-
The packed row polynomial at a sixth root, as an ordinary polynomial in the free core.

At a row `w = u·g⁶` of a natural state (mask `m`, packing `A = 1`), every factor of `positiveSlotRow` is an
ordinary polynomial `∑_I c(I)·idealRowHom u I` with coefficients common to all cores `u` at the root `g`:
`rowWeight η m 1 (u g⁶) t I = rootCommon η m g t I · idealRowHom u I`.
-/
import Submissions.arvi_selected_leaf.R1.OrdPoly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedEnergy

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy CenteredMomentSourceMass
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

/-- The coefficient common to all cores at the root `g`. -/
def rootCommon (η : Character) (m g : O) (t : ℝ) (I : Ideal O) : ℂ :=
  idealCoeff η I * idealRowHom (m^6 * g^6) I * (Ideal.absNorm I : ℂ)^(Complex.I*t)

theorem rootCommon_norm_le (η : Character) (m g : O) (t : ℝ) (I : Ideal O) :
    ‖rootCommon η m g t I‖ ≤ 1 := by
  unfold rootCommon
  rw [norm_mul, norm_mul]
  have h1 := idealCoeff_norm_le_one η I
  have h2 := idealRowHom_norm (m^6 * g^6) I
  have h3 : ‖(Ideal.absNorm I : ℂ)^(Complex.I*t)‖ ≤ 1 := by
    by_cases hI : Ideal.absNorm I = 0
    · rw [hI]; simp only [Nat.cast_zero]
      by_cases ht : Complex.I * t = 0
      · rw [ht, Complex.cpow_zero, norm_one]
      · rw [Complex.zero_cpow ht, norm_zero]; norm_num
    · have hpos : (0:ℝ) < (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hI
      rw [show ((Ideal.absNorm I : ℕ) : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp
  calc ‖idealCoeff η I‖ * ‖idealRowHom (m^6 * g^6) I‖ * ‖(Ideal.absNorm I : ℂ)^(Complex.I*t)‖
      ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

/-- **Row weight at a sixth root.** -/
theorem rowWeight_root (η : Character) (m u g : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m 1 (u * g^6) t I = rootCommon η m g t I * idealRowHom u I := by
  change (idealCoeff η I * idealRowHom (m^6 * (1 * (u * g^6))) I) *
      (Ideal.absNorm I : ℂ)^(Complex.I*t) = _
  rw [show m^6 * (1 * (u * g^6)) = (m^6 * g^6) * u by ring, idealRowHom_argument_mul]
  unfold rootCommon
  ring

/-- **The slot at a sixth root** as an ordinary polynomial in the core. -/
theorem normalizedSlot_root (η : Character) (m u g : O) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (t P : ℝ) :
    normalizedSlot η m 1 (u * g^6) S β t P =
      ordinaryPolynomial S (fun I => (Real.sqrt P : ℂ)⁻¹ * β I.val * rootCommon η m g t I.val) u := by
  unfold normalizedSlot
  rw [rowSlot_eq_weight, ordinaryPolynomial,
    Finset.sum_coe_sort S (fun I => (Real.sqrt P : ℂ)⁻¹ * β I * rootCommon η m g t I *
      idealRowHom u I), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [rowWeight_root]
  ring

/-- **The plain sum at a sixth root** as an ordinary polynomial on the ideal ball of radius `bX`. -/
theorem rowTwistedSum_root (η : Character) (m u g : O) (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    rowTwistedSum η m 1 (u * g^6) W t X =
      ordinaryPolynomial (idealBall (b*X))
        (fun I => rootCommon η m g t I.val * W ((Ideal.absNorm I.val : ℝ)/X)) u := by
  rw [rowTwistedSum_eq_weight, ordinaryPolynomial,
    Finset.sum_coe_sort (idealBall (b*X)) (fun I => rootCommon η m g t I * W ((Ideal.absNorm I : ℝ)/X) *
      idealRowHom u I)]
  rw [tsum_eq_sum (s := idealBall (b*X))]
  · apply Finset.sum_congr rfl
    intro I _
    rw [rowWeight_root]
    ring
  · intro I hI
    rw [mem_idealBall, not_and_or] at hI
    rcases hI with hI | hI
    · rw [not_not] at hI
      rw [hI, map_zero, zero_mul]
    · have hW : W ((Ideal.absNorm I : ℝ)/X) = 0 := by
        by_contra hne
        have h1 := hs hne
        simp only [Set.mem_Iic] at h1
        rw [div_le_iff₀ hX] at h1
        exact hI h1
      rw [hW, mul_zero]

end
end QRH.ArviSelectedLeaf.R1
