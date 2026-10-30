/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.DetectorWords
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate

/-!
Whole finite words in the actual ordinary-ideal row feature. All repeated
prime factors and all common coefficient masks stay in the convolution.
The divisor estimate is applied once to the entire word: the requested
power loss is independent of the later finite word degree.

These lemmas prove the coefficient and response inputs to inverse
amplification. Selecting enough positive slot width, and composing the
result with reflection and contraction, remain separate obligations.
-/
namespace Qrh.JointDetector.WholeWordAmplification
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentAddedZero CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentWholeSlotDeletion
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def normalizedSlotCoefficient (η : HeckeFamily.Character) (m A : O)
    (β : Ideal O → ℂ) (t P : ℝ) (I : Ideal O) : ℂ :=
  (Real.sqrt P : ℂ)⁻¹ * slotCoefficient η m A β t I

theorem normalizedSlot_polynomial (η : HeckeFamily.Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (t P : ℝ) :
    normalizedSlot η m A z S β t P =
      ∑ I ∈ S, normalizedSlotCoefficient η m A β t P I * idealRowHom z I := by
  rw [normalizedSlot_common_coefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  unfold normalizedSlotCoefficient
  ring

/-- Height phases, common root/gcd masks and anchor factors have norm at most
one. Their modulus does not enter the normalized coefficient mass. -/
theorem normalizedSlotCoefficient_square (η : HeckeFamily.Character) (m A : O)
    (β : Ideal O → ℂ) (t P B : ℝ) (I : Ideal O) (hI : I ≠ 0)
    (hP : 0 < P) (hβ : ‖β I‖ ≤ B) :
    ‖normalizedSlotCoefficient η m A β t P I‖^2 ≤ B^2/P := by
  have hs : ‖slotCoefficient η m A β t I‖ ≤ B := by
    rw [slotCoefficient, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t I hI)).trans hβ
  have hsq : ‖slotCoefficient η m A β t I‖^2 ≤ B^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hs 2
  calc
    _ = P⁻¹ * ‖slotCoefficient η m A β t I‖^2 := by
      simp only [normalizedSlotCoefficient, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg P), mul_pow,
        inv_pow, Real.sq_sqrt hP.le]
    _ ≤ P⁻¹ * B^2 := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hP.le)
    _ = _ := by ring

theorem normalizedSlotCoefficient_mass (η : HeckeFamily.Character) (m A : O)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (t P b B : ℝ)
    (hP : 0 < P) (hsize : 1 ≤ b*P)
    (hzero : ∀ I ∈ S, I ≠ 0) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ b*P)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ B) :
    (∑ I ∈ S, ‖normalizedSlotCoefficient η m A β t P I‖^2) ≤ 128*b*B^2 := by
  have hcard := DescentFiberCost.finite_ideal_count_real S (b*P)
    hsize hzero hN
  calc
    _ ≤ ∑ _I ∈ S, B^2/P := Finset.sum_le_sum fun I hI =>
      normalizedSlotCoefficient_square η m A β t P B I (hzero I hI) hP (hβ I hI)
    _ = (S.card : ℝ)*(B^2/P) := by simp
    _ ≤ (128*(b*P))*(B^2/P) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg (sq_nonneg _) hP.le)
    _ = _ := by field_simp

/-- Cauchy on complete product fibres, followed by exact finite regrouping. -/
theorem tupleCoefficient_square_mass {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (D : ℝ)
    (hfiber : ∀ I ∈ tupleColumns S,
      ((S.filter fun v => tupleProduct v = I).card : ℝ) ≤ D) :
    (∑ I ∈ tupleColumns S, ‖tupleCoefficient S β I‖^2) ≤
      D * ∑ v ∈ S, ‖β v‖^2 := by
  have hlocal (I : Ideal O) (hI : I ∈ tupleColumns S) :
      ‖tupleCoefficient S β I‖^2 ≤
        D * ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖^2 := by
    let fiber := S.filter (fun v => tupleProduct v = I)
    have hc := coefficient_cauchy (fun (_ : fiber) => (1:ℂ)) (fun v => β v.val)
    have hc' : ‖tupleCoefficient S β I‖^2 ≤
        (fiber.card : ℝ) * ∑ v ∈ fiber, ‖β v‖^2 := by
      simpa only [tupleCoefficient, one_mul, norm_one, one_pow,
        Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
        Fintype.card_coe, Finset.sum_coe_sort fiber (fun v => β v),
        Finset.sum_coe_sort fiber (fun v => ‖β v‖^2), fiber] using hc
    exact hc'.trans (mul_le_mul_of_nonneg_right (hfiber I hI)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ I ∈ tupleColumns S,
        D * ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖^2 :=
      Finset.sum_le_sum hlocal
    _ = D * ∑ I ∈ tupleColumns S,
        ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖^2 := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

def wordDivisorConstant (r : ℕ) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (idealDivisorConstant (ε/(r+1)) (by positivity))^r

theorem wordDivisorConstant_pos (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < wordDivisorConstant r ε hε :=
  pow_pos (idealDivisorConstant_pos _ _) _

/-- The whole word costs X^ε, even when its finite degree is chosen later. -/
theorem tuple_product_fiber_small_power {r : ℕ} (S : Finset (Fin r → Ideal O))
    (I : Ideal O) (hI : I ≠ 0) (ε X : ℝ) (hε : 0 < ε) (hX : 1 ≤ X)
    (hN : (Ideal.absNorm I : ℝ) ≤ X) :
    ((S.filter fun v => tupleProduct v = I).card : ℝ) ≤
      wordDivisorConstant r ε hε * X^ε := by
  let a : ℝ := ε/(r+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hD : 0 ≤ idealDivisorConstant a ha := (idealDivisorConstant_pos a ha).le
  have hf : ((idealDivisors I).card : ℝ) ≤ idealDivisorConstant a ha * X^a :=
    (idealDivisorConstant_bound a ha I hI).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hN ha.le) hD)
  have hexp : a*(r:ℝ) ≤ ε := by
    dsimp [a]
    have hr : (0:ℝ) ≤ r := Nat.cast_nonneg _
    have hd : (0:ℝ) < r+1 := by positivity
    have he : ε/(r+1)*(r:ℝ) = (ε*(r:ℝ))/(r+1) := by ring
    rw [he]
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^r := by
      exact_mod_cast tuple_product_fiber_card S I hI
    _ ≤ (idealDivisorConstant a ha * X^a)^r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hf r
    _ = (idealDivisorConstant a ha)^r * X^(a*(r:ℝ)) := by
      rw [mul_pow, Real.rpow_mul_natCast (by linarith : 0 ≤ X)]
    _ ≤ (idealDivisorConstant a ha)^r * X^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp)
        (pow_nonneg hD _)
    _ = _ := rfl

theorem tupleCoefficient_square_mass_small_power {r : ℕ}
    (S : Finset (Fin r → Ideal O)) (β : (Fin r → Ideal O) → ℂ)
    (ε X : ℝ) (hε : 0 < ε) (hX : 1 ≤ X)
    (hzero : ∀ I ∈ tupleColumns S, I ≠ 0)
    (hN : ∀ I ∈ tupleColumns S, (Ideal.absNorm I : ℝ) ≤ X) :
    (∑ I ∈ tupleColumns S, ‖tupleCoefficient S β I‖^2) ≤
      (wordDivisorConstant r ε hε * X^ε) * ∑ v ∈ S, ‖β v‖^2 :=
  tupleCoefficient_square_mass S β _ fun I hI =>
    tuple_product_fiber_small_power S I (hzero I hI) ε X hε hX (hN I hI)

def wordTuples {r : ℕ} (pools : Fin r → Finset (Ideal O)) :
    Finset (Fin r → Ideal O) := Fintype.piFinset pools

def wordCoefficient {r : ℕ} (c : Fin r → Ideal O → ℂ)
    (v : Fin r → Ideal O) : ℂ := ∏ i, c i (v i)

theorem word_unmerged_square_mass {r : ℕ}
    (pools : Fin r → Finset (Ideal O)) (c : Fin r → Ideal O → ℂ) :
    (∑ v ∈ wordTuples pools, ‖wordCoefficient c v‖^2) =
      ∏ i, ∑ I ∈ pools i, ‖c i I‖^2 := by
  simp only [wordTuples, wordCoefficient, norm_prod, ← Finset.prod_pow]
  exact (Finset.prod_univ_sum pools (fun i I => ‖c i I‖^2)).symm

theorem word_square_mass {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (c : Fin r → Ideal O → ℂ) (C : Fin r → ℝ)
    (hC : ∀ i, (∑ I ∈ pools i, ‖c i I‖^2) ≤ C i)
    (ε X : ℝ) (hε : 0 < ε) (hX : 1 ≤ X)
    (hzero : ∀ I ∈ tupleColumns (wordTuples pools), I ≠ 0)
    (hN : ∀ I ∈ tupleColumns (wordTuples pools), (Ideal.absNorm I : ℝ) ≤ X) :
    (∑ I ∈ tupleColumns (wordTuples pools),
      ‖tupleCoefficient (wordTuples pools) (wordCoefficient c) I‖^2) ≤
      (wordDivisorConstant r ε hε * X^ε) * ∏ i, C i := by
  have hp : (∏ i, ∑ I ∈ pools i, ‖c i I‖^2) ≤ ∏ i, C i :=
    Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (fun i _ => hC i)
  exact (tupleCoefficient_square_mass_small_power (wordTuples pools)
    (wordCoefficient c) ε X hε hX hzero hN).trans
      (mul_le_mul_of_nonneg_left (by rwa [word_unmerged_square_mass])
        (mul_nonneg (wordDivisorConstant_pos r ε hε).le
          (Real.rpow_nonneg (by linarith : 0 ≤ X) _)))

/-- The merged source retains every ordinary ideal product, including all
shared-prime powers. Coefficients are common to the whole selected row set. -/
theorem word_polynomial {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (c : Fin r → Ideal O → ℂ) (z : O) :
    (∏ i, ∑ I ∈ pools i, c i I * idealRowHom z I) =
      ∑ I ∈ tupleColumns (wordTuples pools),
        tupleCoefficient (wordTuples pools) (wordCoefficient c) I * idealRowHom z I := by
  rw [Finset.prod_univ_sum]
  change (∑ v ∈ wordTuples pools, ∏ i, c i (v i)*idealRowHom z (v i)) = _
  rw [← tuple_weighted_regroup]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [wordCoefficient, tupleProduct, map_prod, Finset.prod_mul_distrib]

theorem word_response {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (c : Fin r → Ideal O → ℂ) (R : Fin r → ℝ) (z : O)
    (hR : ∀ i, 0 ≤ R i)
    (hresponse : ∀ i, R i ≤ ‖∑ I ∈ pools i, c i I * idealRowHom z I‖^2) :
    (∏ i, R i) ≤ ‖∑ I ∈ tupleColumns (wordTuples pools),
      tupleCoefficient (wordTuples pools) (wordCoefficient c) I * idealRowHom z I‖^2 := by
  rw [← word_polynomial, norm_prod, ← Finset.prod_pow]
  exact Finset.prod_le_prod₀ (fun i _ => hR i) (fun i _ => hresponse i)

theorem word_response_rpow {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (c : Fin r → Ideal O → ℂ) (energy : Fin r → ℝ) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (hresponse : ∀ i, Z^(energy i) ≤ ‖∑ I ∈ pools i, c i I * idealRowHom z I‖^2) :
    Z^(∑ i, energy i) ≤ ‖∑ I ∈ tupleColumns (wordTuples pools),
      tupleCoefficient (wordTuples pools) (wordCoefficient c) I * idealRowHom z I‖^2 := by
  have h := word_response pools c (fun i => Z^(energy i)) z
    (fun _ => Real.rpow_nonneg hZ.le _) hresponse
  rwa [← Real.rpow_sum_of_pos hZ] at h

/-- A closed inverse-amplification inequality for an actual common prime word.
Only the literal individual responses and coefficient masses are inputs;
the merged-word response, full convolution mass and merge multiplicity are
proved here. The whole-word degree affects the constant, not ε.
-/
theorem selectedNorm_word_inverse_amplification {r : ℕ}
    (rows : Finset O) (sources merged : Finset (Ideal O))
    (pools : Fin r → Finset (Ideal O)) (c : Fin r → Ideal O → ℂ)
    (C energy : Fin r → ℝ) (Z X Y ε : ℝ)
    (hZ : 0 < Z) (hX : 1 ≤ X) (hY : 0 ≤ Y) (hε : 0 < ε)
    (hclosed : ∀ I ∈ sources, ∀ J ∈ tupleColumns (wordTuples pools), I*J ∈ merged)
    (hmass : ∀ i, (∑ I ∈ pools i, ‖c i I‖^2) ≤ C i)
    (hresponse : ∀ z ∈ rows, ∀ i,
      Z^(energy i) ≤ ‖∑ I ∈ pools i, c i I * idealRowHom z I‖^2)
    (hwordZero : ∀ I ∈ tupleColumns (wordTuples pools), I ≠ 0)
    (hwordNorm : ∀ I ∈ tupleColumns (wordTuples pools), (Ideal.absNorm I : ℝ) ≤ X)
    (hmergedZero : ∀ I ∈ merged, I ≠ 0)
    (hmergedNorm : ∀ I ∈ merged, (Ideal.absNorm I : ℝ) ≤ Y) :
    selectedNorm rows sources ≤
      ((wordDivisorConstant r ε hε*X^ε)*∏ i, C i)*
        idealDivisorConstant ε hε * Y^ε * selectedNorm rows merged /
          Z^(∑ i, energy i) := by
  have hC (i : Fin r) : 0 ≤ C i :=
    (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hmass i)
  have hmass' := word_square_mass pools c C hmass ε X hε hX hwordZero hwordNorm
  have hmass'' : (∑ I : tupleColumns (wordTuples pools),
      ‖tupleCoefficient (wordTuples pools) (wordCoefficient c) I.val‖^2) ≤
      (wordDivisorConstant r ε hε*X^ε)*∏ i, C i := by
    rw [Finset.sum_coe_sort _ (fun I =>
      ‖tupleCoefficient (wordTuples pools) (wordCoefficient c) I‖^2)]
    exact hmass'
  have hresponse' (z : rows) : Z^(∑ i, energy i) ≤
      ‖∑ I : tupleColumns (wordTuples pools),
        tupleCoefficient (wordTuples pools) (wordCoefficient c) I.val *
          idealRowHom z.val I.val‖^2 := by
    rw [Finset.sum_coe_sort _ (fun I =>
      tupleCoefficient (wordTuples pools) (wordCoefficient c) I * idealRowHom z.val I)]
    exact word_response_rpow pools c energy z.val Z hZ (hresponse z.val z.property)
  exact selectedNorm_inverse_amplification_small_power rows sources
    (tupleColumns (wordTuples pools)) merged hclosed
    (fun I => tupleCoefficient (wordTuples pools) (wordCoefficient c) I.val)
    (Z^(∑ i, energy i)) ((wordDivisorConstant r ε hε*X^ε)*∏ i, C i) Y ε
    (Real.rpow_pos_of_pos hZ _)
    (mul_nonneg (mul_nonneg (wordDivisorConstant_pos r ε hε).le
      (Real.rpow_nonneg (by linarith : 0 ≤ X) _))
      (Finset.prod_nonneg fun i _ => hC i)) hY hε hresponse' hmass''
    hmergedZero hmergedNorm

end
end Qrh.JointDetector.WholeWordAmplification

#print axioms Qrh.JointDetector.WholeWordAmplification.word_square_mass
#print axioms Qrh.JointDetector.WholeWordAmplification.normalizedSlotCoefficient_mass
#print axioms Qrh.JointDetector.WholeWordAmplification.word_polynomial
#print axioms Qrh.JointDetector.WholeWordAmplification.word_response
#print axioms Qrh.JointDetector.WholeWordAmplification.selectedNorm_word_inverse_amplification
