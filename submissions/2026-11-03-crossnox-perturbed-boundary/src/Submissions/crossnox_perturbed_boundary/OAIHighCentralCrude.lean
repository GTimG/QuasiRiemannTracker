/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighCentralCrude.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale_with_perturbed_lengths
    {Z a e t : ℝ} (hZ : 1 ≤ Z) (ha : 0 ≤ a) (he : 0 ≤ e)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 30) :
    (Z ^ (AsymmetricGeometry.xBase - t / 2 : ℝ)) ^ (1 / 2 - (17 / 50 : ℝ)) *
      Z ^ (2 + (17 / 50 : ℝ) - 1) *
      (Z ^ (AsymmetricGeometry.yBase - t / 2 : ℝ)) ^ ((1 - a - 6 * e) - 1) ≤ Z ^ (2 : ℝ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [← Real.rpow_mul hZ0.le]
  rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hly : 0 ≤ (AsymmetricGeometry.yBase : ℝ) - t / 2 := by linarith
  have hneg : ((AsymmetricGeometry.yBase : ℝ) - t / 2) * (-a - 6 * e) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hly (by linarith)
  nlinarith

lemma central_prime_product_bound_with_perturbed_lengths {K : ℕ}
    (P : Fin K → PrimeIdeal) (Z b t : ℝ) (hZ : 0 < Z) (_hb : 0 ≤ b)
    (length : Fin K → ℝ) (hlength : ∑ j, length j = (1 / 6 : ℝ) + t)
    (hP : ∀ j, ((P j).val.absNorm : ℝ) ≤ b * Z ^ (length j)) :
    (∏ j, ((P j).val.absNorm : ℝ)) ≤ b ^ K * Z ^ ((1 / 6 : ℝ) + t) := by
  calc
    _ ≤ ∏ j, b * Z ^ (length j) :=
      Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hP j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.rpow_sum_of_pos hZ, hlength]

lemma central_arithmetic_cost_bound_with_perturbed_lengths {K : ℕ}
    (η : Character) (u : FreeRow) (P : Fin K → PrimeIdeal)
    (Z b ζ t : ℝ) (hZ : 1 ≤ Z) (hb : 0 ≤ b)
    (hζ : ζ ≤ 1 / 48) (ht' : t ≤ 1 / 30)
    (hu : ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤
      Z ^ ((AsymmetricGeometry.rowBase : ℝ) + 3 * t / 2 + ζ))
    (length : Fin K → ℝ) (hlength : ∑ j, length j = (1 / 6 : ℝ) + t)
    (hP : ∀ j, ((P j).val.absNorm : ℝ) ≤ b * Z ^ (length j)) :
    contourArithmeticCost η u P ≤
      (η.modulus.absNorm : ℝ) ^ 2 * (b ^ K) ^ 3 * Z ^ (7 : ℝ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ Z :=
    hu.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hZ
        (show (AsymmetricGeometry.rowBase : ℝ) + 3 * t / 2 + ζ ≤ 1 by linarith))
  have hp := central_prime_product_bound_with_perturbed_lengths
    P Z b t hZ0 hb length hlength hP
  have hp0 : 0 ≤ ∏ j, ((P j).val.absNorm : ℝ) :=
    Finset.prod_nonneg (fun j _ => Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm : ℝ) ^ 2 * Z ^ 6 *
        (b ^ K * Z ^ ((1 / 6 : ℝ) + t)) ^ 3 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3)
        (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = (η.modulus.absNorm : ℝ) ^ 2 * (b ^ K) ^ 3 *
        (Z ^ (6 : ℝ) * Z ^ (((1 / 6 : ℝ) + t) * 3)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hZ0.le, ← Real.rpow_natCast Z 6]
      norm_num only [Nat.cast_ofNat]
      ring
    _ ≤ _ := by
      have hpow : Z ^ (6 : ℝ) * Z ^ (((1 / 6 : ℝ) + t) * 3) ≤ Z ^ (7 : ℝ) := by
        rw [← Real.rpow_add hZ0]
        exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem original_row_rectangle_arbitrary_saving_with_perturbed_lengths (K : ℕ) (τ saving b ζ t : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (ht : 0≤t) (ht' : t≤1/30)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((AsymmetricGeometry.rowBase:ℝ)+3*t/2+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ)+t →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(AsymmetricGeometry.xBase-t/2:ℝ)) (Z^(AsymmetricGeometry.yBase-t/2:ℝ)) Z u-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 (Z^(AsymmetricGeometry.xBase-t/2:ℝ)) (Z^(AsymmetricGeometry.yBase-t/2:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((9:ℝ)+saving)/τ)
  have hN' : (9:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(AsymmetricGeometry.xBase-t/2:ℝ)) (Z^(AsymmetricGeometry.yBase-t/2:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound_with_perturbed_lengths η u P Z b ζ t hZ hb.le hζ ht' huZ length hl hp
  have hscale := central_source_crude_scale_with_perturbed_lengths hZ (by linarith : 0≤a) he.le ht ht'
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(9:ℝ)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(7:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(9:ℝ)/height H^N) := by
      have hh : Z^(7:ℝ)*Z^(2:ℝ)=Z^(9:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(9:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


end SevenEighths.ProbeHighRowFamily
end

end OAI
