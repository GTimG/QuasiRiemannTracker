/-
Small facts for the assembly of R1: lengths, prime annulus pools and their slots, annular weights, and norms of
sixth-root rows.
-/
import Submissions.arvi_selected_leaf.R1.RootBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot HeckePrimeAnnular
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

/-- `Z` to the length is `max 1 X`. -/
theorem rpow_length (Z X : ℝ) (hZ : 1 < Z) :
    Z^(CenteredMomentEnergyBands.length Z X) = max 1 X := by
  unfold CenteredMomentEnergyBands.length
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ) (zero_lt_one.trans_le (le_max_left _ _))

theorem max_one_mul_le (c X : ℝ) (hc : 1 ≤ c) : max 1 (c*X) ≤ c * max 1 X := by
  apply max_le
  · nlinarith [le_max_left (1:ℝ) X]
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)

/-- **An annular slot coefficient is bounded by the profile.** -/
theorem annular_coeff_le (χ : Character) (W : ℝ → ℂ) (LW D σ f : ℝ) (I : Ideal O) (_hD : 0 < D)
    (hσ : 0 ≤ σ) (hs : Function.support W ⊆ Set.Icc 1 2) (hW : ∀ x, ‖W x‖ ≤ LW) :
    ‖idealCoeff χ I * annularWeight W D σ f I‖ ≤ LW := by
  have hLW : 0 ≤ LW := (norm_nonneg _).trans (hW 0)
  unfold annularWeight
  by_cases h0 : W ((I.absNorm : ℝ)/D) = 0
  · rw [h0]; simpa using hLW
  · have hx := hs h0
    have hx1 : (1:ℝ) ≤ (I.absNorm : ℝ)/D := hx.1
    have hxpos : 0 < (I.absNorm : ℝ)/D := zero_lt_one.trans_le hx1
    have hph : ‖(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ f)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      simp only [Complex.neg_re, HeckeDyadic.shift_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [norm_mul, norm_mul]
    calc ‖idealCoeff χ I‖ * (‖W ((I.absNorm : ℝ)/D)‖ *
          ‖(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ f)‖)
        ≤ 1 * (LW * 1) := by
          apply mul_le_mul (idealCoeff_norm_le_one χ I) _ (by positivity) zero_le_one
          exact mul_le_mul (hW _) hph (norm_nonneg _) hLW
      _ = LW := by ring

/-- Sources of a prime annulus pool are nonzero of norm at most `2D`. -/
theorem primePool_mem (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ) (D : ℝ) (hD : 0 ≤ D)
    (I : Ideal O) (hI : I ∈ primePool rayM H 2 D) : I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 2 * D := by
  simp only [primePool] at hI
  rw [Finset.mem_filter] at hI
  obtain ⟨hann, hprime, _⟩ := hI
  refine ⟨hprime.ne_zero, ?_⟩
  have h := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hann).2
  have h' : (Ideal.absNorm I : ℝ) ≤ max 1 2 * D :=
    (Nat.cast_le.mpr h).trans (Nat.floor_le (by positivity))
  have h2 : max (1:ℝ) 2 = 2 := by norm_num
  rwa [h2] at h'

theorem primePool_card_le (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ) (D : ℝ) (hD : 0 ≤ D) :
    ((primePool rayM H 2 D).card : ℝ) ≤ 256 * D := by
  have h := ideal_card_le (primePool rayM H 2 D) (2*D) (by positivity)
    (fun I hI => (primePool_mem rayM H D hD I hI).1) (fun I hI => (primePool_mem rayM H D hD I hI).2)
  linarith

/-- The norm bound of a prime annulus slot at scale `D ≥ 1/2`. -/
theorem primeSlot_normLe (η : Character) (m g : O) (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ)
    (β : Ideal O → ℂ) (t D : ℝ) (hD : 1/2 ≤ D) :
    (slotPoly η m g (primePool rayM H 2 D) β t D).NormLe (2*D) ∧ 1 ≤ 2*D := by
  refine ⟨?_, by linarith⟩
  intro I hI
  exact primePool_mem rayM H D (by linarith) I hI

/-- The mass of a prime annulus slot with coefficients at most `LW`. -/
theorem primeSlot_mass_le (η : Character) (m g : O) (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ)
    (β : Ideal O → ℂ) (t D LW : ℝ) (hD : 0 < D) (hβ : ∀ I ∈ primePool rayM H 2 D, ‖β I‖ ≤ LW) :
    (slotPoly η m g (primePool rayM H 2 D) β t D).mass ≤ 256 * LW^2 := by
  have h := slotPoly_mass_le η m g (primePool rayM H 2 D) β t D LW (256 * D) hD hβ
    (primePool_card_le rayM H D hD.le)
  calc _ ≤ 256 * D * LW^2 / D := h
    _ = 256 * LW^2 := by field_simp

/-- The square of a prime annulus slot. -/
theorem primeSlot_sq_le (η : Character) (m A z : O) (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ)
    (β : Ideal O → ℂ) (t D LW : ℝ) (hD : 0 < D) (hLW : 0 ≤ LW)
    (hβ : ∀ I ∈ primePool rayM H 2 D, ‖β I‖ ≤ LW) :
    ‖normalizedSlot η m A z (primePool rayM H 2 D) β t D‖^2 ≤ 256^2 * LW^2 * D := by
  have h := slot_norm_sq_le η m A z (primePool rayM H 2 D) β t D hD LW (256 * D) hLW hβ
    (primePool_card_le rayM H D hD.le)
  calc _ ≤ (256 * D)^2 * LW^2 / D := h
    _ = 256^2 * LW^2 * D := by field_simp

/-- The norm of a sixth-root row. -/
theorem absNorm_rowMap (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal) :
    ((Ideal.span {rowMap p}).absNorm : ℝ) =
      ((Ideal.span {p.1.val}).absNorm : ℝ) * (p.2.val.absNorm : ℝ)^6 := by
  rw [rowMap_span, map_mul, map_pow]
  push_cast
  ring

theorem rootNorm_generator (r : HeckeInverseAmplification.NonzeroIdeal) :
    ((Ideal.span {ConcretePrimeRowBridge.idealGenerator r.val}).absNorm : ℝ) = rootNorm r := by
  rw [ConcretePrimeRowBridge.span_idealGenerator]
  rfl

end
end QRH.ArviSelectedLeaf.R1
