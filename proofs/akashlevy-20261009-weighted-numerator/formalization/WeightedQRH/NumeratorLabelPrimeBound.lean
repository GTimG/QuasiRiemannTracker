import WeightedQRH.NumeratorLabelPacket
import WeightedQRH.NumeratorErrorPrimeSum

/-! All physical error labels have the same Y^(-4/25) factor as a main prime
slot. Constants are uniform over subsets of a fixed finite slot family. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem error_label_prime_product_bound (epsilon c d B : ℝ) (K : ℕ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ K → ∀ (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
      (Y : ι → ℝ) (W : ι → ℝ → ℂ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ z : ℂ, z.re = 17 / 50 →
      (∏ i, ∑ P : T i, 2880 *
        ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) * (P.val.val.absNorm : ℂ)^(z-1)‖ *
          errorSize u P.val) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon *
          ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  let eta : ℝ := epsilon / (K+1)
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  obtain ⟨C0,hC0,hslot⟩ := error_coefficient_slot_sum eta c d B heta hc hd hB
  let C1 : ℝ := max 1 (2880*C0)
  have hC1 : 1 ≤ C1 := le_max_left _ _
  have hC1pos : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C1^K,pow_pos hC1pos _,?_⟩
  intro ι _ _ hcard u T Y W hY hWS hWB z hz
  let Nu : ℝ := (Ideal.span {u.val} : Ideal O).absNorm
  have hNu : 1 ≤ Nu := by
    have hn : (Ideal.span {u.val} : Ideal O).absNorm ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    dsimp only [Nu]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hNupos : 0 < Nu := lt_of_lt_of_le zero_lt_one hNu
  have hEach (i : ι) :
      (∑ P : T i, 2880 * ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) *
        (P.val.val.absNorm : ℂ)^(z-1)‖ * errorSize u P.val) ≤
      C1 * Nu^eta * (Y i)^(-(4 / 25 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (hslot u (T i) (Y i) (hY i) (W i) (hWS i) (hWB i) z hz)
      (show (0 : ℝ) ≤ 2880 by norm_num)
    calc
      _ = 2880 * (∑ P : T i, ‖W i ((P.val.val.absNorm : ℝ)/(Y i)) *
          (P.val.val.absNorm : ℂ)^(z-1)‖ * errorSize u P.val) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro P hP; ring
      _ ≤ 2880 * (C0 * Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := hh
      _ ≤ _ := by
        calc
          _ = (2880*C0) * (Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := by ring
          _ ≤ C1 * (Nu^eta * (Y i)^(-(4 / 25 : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (Real.rpow_nonneg hNupos.le _) (Real.rpow_nonneg ((zero_le_one.trans (hY i))) _))
          _ = _ := by ring
  calc
    _ ≤ ∏ i, (C1 * Nu^eta * (Y i)^(-(4 / 25 : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun P _ => mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
          (errorSize_nonneg u P.val))
      · intro i hi
        exact hEach i
    _ = C1^(Fintype.card ι) * Nu^(eta*(Fintype.card ι : ℝ)) *
        ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_pow]
      rw [show (Nu^eta)^(Fintype.card ι) = Nu^(eta*(Fintype.card ι : ℝ)) by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNupos.le]]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (zero_le_one.trans (hY i)) _))
      apply mul_le_mul (pow_le_pow_right₀ hC1 hcard) _ (Real.rpow_nonneg hNupos.le _) (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hNu
      dsimp only [eta]
      have hcardR : (Fintype.card ι : ℝ) ≤ K := by exact_mod_cast hcard
      have hden : (0 : ℝ) < K+1 := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith

end WeightedQRH.Numerator
