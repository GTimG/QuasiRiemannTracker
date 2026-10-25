/- Copyright (c) 2026 Sil. Apache-2.0.
The correction B/H removes a common ordinary prime from the fifth-free row.
Its mass is bounded at the reflected exponents 2/3 and 1/3 as well as centrally.
The uniform constant is paid only over the prescribed fixed prime support.
-/
import Candidate.SilPrior.FourthPower.KernelSelectedLocal
import Candidate.SilPrior.FourthPower.KernelFixedSupportMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.KernelPunctureMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open KernelFormal KernelInverseCoefficients KernelSeriesMass KernelSelectedMass
local notation "Id" => Ideal ActualEisensteinCubic.O

def correction : LocalSeries := LocalKernels.base formalX formalY*reciprocalSeries

/-- A sharper coefficient majorant is needed beyond the central radius 2/5. -/
theorem reciprocal_coeff_sharp (n : Exponent) :
    |(reciprocalCoeff n : ℝ)| ≤ (5/3 : ℝ)^(degree n) := by
  have aux : ∀ d : ℕ, ∀ n : Exponent, degree n=d →
      |(reciprocalCoeff n : ℝ)| ≤ (5/3 : ℝ)^d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro n hn
      by_cases hz : d=0
      · have hn0 : n=0 := by
          apply (exponent_zero_iff n).mpr
          unfold degree at hn
          omega
        subst n
        simp [reciprocalCoeff_zero,hz]
      have hn0 : n ≠ 0 := by
        intro he
        simp [he,degree] at hn
        omega
      by_cases hd : d < 5
      · rw [reciprocalCoeff_small_degree n hn0 (by omega)]
        simp only [Int.cast_zero,abs_zero]
        positivity
      have hd5 : 5 ≤ d := by omega
      have hshift (i : Fin 11) :
          |(shiftCoeff n (KernelForwardMass.ordinaryExponent i.succ).1
            (KernelForwardMass.ordinaryExponent i.succ).2 : ℝ)| ≤ (5/3 : ℝ)^(d-5) := by
        by_cases hle : exponent (KernelForwardMass.ordinaryExponent i.succ).1
            (KernelForwardMass.ordinaryExponent i.succ).2 ≤ n
        · rw [shiftCoeff,ite_eq_left hle]
          have he := degree_sub_exponent n _ _ hle
          have hi := nonconstant_degree i
          have hlt : degree (n-exponent (KernelForwardMass.ordinaryExponent i.succ).1
              (KernelForwardMass.ordinaryExponent i.succ).2) < d := by omega
          have hpow : degree (n-exponent (KernelForwardMass.ordinaryExponent i.succ).1
              (KernelForwardMass.ordinaryExponent i.succ).2) ≤ d-5 := by omega
          exact (ih _ hlt _ rfl).trans (pow_le_pow_right₀ (by norm_num) hpow)
        · rw [shiftCoeff,ite_eq_right hle]
          simp only [Int.cast_zero,abs_zero]
          positivity
      calc
        _ ≤ ∑ i : Fin 11, |(shiftCoeff n (KernelForwardMass.ordinaryExponent i.succ).1
            (KernelForwardMass.ordinaryExponent i.succ).2 : ℝ)| := reciprocal_abs_recurrence n hn0
        _ ≤ ∑ _i : Fin 11, (5/3 : ℝ)^(d-5) := Finset.sum_le_sum (fun i _ => hshift i)
        _ = 11*(5/3 : ℝ)^(d-5) := by simp
        _ ≤ (5/3 : ℝ)^5*(5/3 : ℝ)^(d-5) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (5/3 : ℝ)^d := by rw [← pow_add,Nat.add_sub_of_le hd5]
  exact aux (degree n) n rfl

theorem reciprocal_mass_wide {z : ℝ} (hz : 0 ≤ z) (hcap : z ≤ 11/20) :
    Summable (weight reciprocalSeries z) ∧ (∑' n, weight reciprocalSeries z n) ≤ 144 := by
  let r : ℝ := (5/3)*z
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrq : r ≤ 11/12 := by dsimp [r]; linarith
  have hr1 : r < 1 := by linarith
  have hg := geometric_pair_sum hr hr1
  have hpoint (ij : ℕ × ℕ) : weight reciprocalSeries z (pairExponent ij) ≤ r^(ij.1+ij.2) := by
    change |(reciprocalCoeff (exponent ij.1 ij.2) : ℝ)| *z^(degree (exponent ij.1 ij.2)) ≤ _
    rw [degree_exponent]
    calc
      _ ≤ (5/3 : ℝ)^(ij.1+ij.2)*z^(ij.1+ij.2) :=
        mul_le_mul_of_nonneg_right (by simpa only [degree_exponent] using
          (reciprocal_coeff_sharp (exponent ij.1 ij.2))) (pow_nonneg hz _)
      _ = _ := (mul_pow _ _ _).symm
  have hs := Summable.of_nonneg_of_le (fun ij => weight_nonneg _ hz (pairExponent ij)) hpoint hg.1
  refine ⟨pairExponent.summable_iff.mp hs,?_⟩
  rw [← pairExponent.tsum_eq (weight reciprocalSeries z)]
  apply (hs.tsum_le_tsum hpoint hg.1).trans
  rw [hg.2]
  have hden : 0 < 1-r := by linarith
  have hinv : (1-r)⁻¹ ≤ 12 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/12)
      (show (1:ℝ)/12 ≤ 1-r by linarith)
    norm_num [one_div] at hh
    exact hh
  have hn : 0 ≤ (1-r)⁻¹ := (inv_pos.mpr hden).le
  nlinarith

def baseExponent : Fin 4 → Exponent :=
  ![exponent 0 0,exponent 1 0,exponent 0 1,exponent 1 1]
def baseCoefficient : Fin 4 → ℤ := ![1,-1,-1,1]

theorem base_expansion : LocalKernels.base formalX formalY =
    ∑ i : Fin 4, MvPowerSeries.monomial (baseExponent i) (baseCoefficient i) := by
  have hm (j k : ℕ) (c : ℤ) :
      MvPowerSeries.monomial (exponent j k) c = c • (formalX^j*formalY^k) := by
    rw [formal_power_monomial,← map_zsmul,zsmul_eq_mul,mul_one]
    simp
  norm_num [baseExponent,baseCoefficient,Fin.sum_univ_succ,hm,LocalKernels.base]
  ring

theorem base_mass {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (weight (LocalKernels.base formalX formalY) z) ∧
      (∑' n, weight (LocalKernels.base formalX formalY) z n) ≤ 4 := by
  rw [base_expansion]
  obtain ⟨hs,hb⟩ := finite_polynomial_mass baseCoefficient baseExponent hz
  refine ⟨hs,hb.trans ?_⟩
  calc
    _ ≤ ∑ _i : Fin 4, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hc : |(baseCoefficient i : ℝ)|=1 := by fin_cases i <;> norm_num [baseCoefficient]
      rw [hc,one_mul]
      exact pow_le_one₀ hz hz1
    _ = 4 := by simp

theorem correction_mass {z : ℝ} (hz : 0 ≤ z) (hcap : z ≤ 11/20) :
    Summable (weight correction z) ∧ (∑' n, weight correction z n) ≤ 576 := by
  have hB := base_mass hz (show z ≤ 1 by linarith)
  have hH := reciprocal_mass_wide hz hcap
  have hm := mass_mul (LocalKernels.base formalX formalY) reciprocalSeries hz hB.1 hH.1
  refine ⟨hm.1,hm.2.trans ?_⟩
  calc
    _ ≤ (4 : ℝ)*144 := mul_le_mul hB.2 hH.2 (tsum_nonneg (weight_nonneg _ hz)) (by norm_num)
    _ = 576 := by norm_num

theorem reflected_radius {p : ℝ} (hp : 7 ≤ p) : p^(-(1/3 : ℝ)) ≤ 11/20 := by
  have hp0 : 0 < p := by linarith
  have hz : 0 ≤ p^(-(1/3 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hc : (p^(-(1/3 : ℝ)))^3 = p⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp0.le]
    norm_num [Real.rpow_neg_one]
  have hinv : p⁻¹ ≤ (7 : ℝ)⁻¹ := (inv_le_inv₀ hp0 (by norm_num)).mpr hp
  by_contra h
  have hh : (11/20 : ℝ)^3 ≤ (p^(-(1/3 : ℝ)))^3 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt (lt_of_not_ge h)) 3
  norm_num at hh
  linarith

/-- One bound covers central and critical reflected weights, with no conductor change. -/
theorem correction_local (P : PrimeIdeal) (hP : Supported P.val) (s t : ℝ)
    (hs : 1/3 ≤ s) (ht : 1/3 ≤ t) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight correction s t P ij) ≤ 576 := by
  have hp : (7 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast KernelInverseIdealMass.supported_prime_norm P hP
  have hp1 : (1 : ℝ) ≤ Ideal.absNorm P.val := by linarith
  let z := (Ideal.absNorm P.val : ℝ)^(-(1/3 : ℝ))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hm := correction_mass hz (reflected_radius hp)
  have hpoint (ij : ℕ × ℕ) : localWeight correction s t P ij ≤ weight correction z (pairExponent ij) := by
    have hx := Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hs)
    have hy := Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg ht)
    simp only [localWeight,weight,pairExponent,Equiv.coe_fn_mk,degree_exponent,pow_add]
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hx _) (abs_nonneg _))
      (pow_le_pow_left₀ (by positivity) hy _) (by positivity) (by positivity)
  have hf := ((pairExponent.summable_iff).mpr hm.1).sum_le_tsum T
    (fun ij _ => weight_nonneg _ hz (pairExponent ij))
  rw [pairExponent.tsum_eq] at hf
  exact (Finset.sum_le_sum (fun ij _ => hpoint ij)).trans (hf.trans hm.2)

def atPrime (H : Finset PrimeIdeal) (P : PrimeIdeal) : LocalSeries :=
  if P ∈ H then correction else 1

theorem unit_local (P : PrimeIdeal) (s t : ℝ) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight 1 s t P ij) ≤ 1 := by
  have he (ij : ℕ × ℕ) : localWeight 1 s t P ij = if ij=(0,0) then 1 else 0 := by
    by_cases h : ij=(0,0)
    · subst ij
      norm_num [localWeight,exponent]
    · have hn : exponent ij.1 ij.2 ≠ 0 := by
        intro hh
        obtain ⟨hi,hj⟩ := (exponent_eq_zero _ _).mp hh
        exact h (Prod.ext hi hj)
      simp [localWeight,MvPowerSeries.coeff_one,hn,h]
  simp_rw [he]
  rw [Finset.sum_ite_eq']
  split_ifs <;> norm_num

theorem fixed_support_ideal_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B →
      ∀ (S H : Finset PrimeIdeal), (∀ P ∈ S, Supported P.val) →
      (∀ P ∈ H, P.val ∣ F) → ∀ (s t : ℝ), 1/3 ≤ s → 1/3 ≤ t →
      ∀ D : Finset (Id × Id), (∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ d ∈ D, idealWeight S (fun P => atPrime H P.val) s t d) ≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := KernelFixedSupportMass.polynomial_support_mass 0 575 B ε
    (by norm_num) (by norm_num) hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ F hF hcut S H hS hH s t hs ht D hd hdS
  have hlocal (P : S) :
      (∑ ij ∈ D.image (fun d => encodePair S d P), localWeight (atPrime H P.val) s t P.val ij) ≤
        if P.val ∈ H then 576 else 1 := by
    dsimp only [atPrime]
    split_ifs
    · exact correction_local P.val (hS P.val P.property) s t hs ht _
    · exact unit_local P.val s t _
  have hprod : (∏ P : S, if P.val ∈ H then (576 : ℝ) else 1) =
      ∏ P ∈ primeValues (S ∩ H), (1+575*(Ideal.absNorm P : ℝ)^(-(0 : ℝ))) := by
    have hco := Finset.prod_coe_sort S (fun P : PrimeIdeal => if P ∈ H then (576 : ℝ) else 1)
    rw [hco,← Finset.prod_filter]
    have he : S.filter (fun P => P ∈ H) = S ∩ H := by ext P; simp
    rw [he]
    unfold primeValues
    rw [Finset.prod_image (by intro P _ Q _ hh; exact Subtype.val_injective hh)]
    norm_num
  calc
    _ ≤ ∏ P : S, ∑ ij ∈ D.image (fun d => encodePair S d P),
        localWeight (atPrime H P.val) s t P.val ij := finite_ideal_product S _ s t D hd hdS
    _ ≤ ∏ P : S, if P.val ∈ H then (576 : ℝ) else 1 :=
      Finset.prod_le_prod₀ (fun P _ => Finset.sum_nonneg
        (fun ij _ => localWeight_nonneg _ _ _ _ _)) (fun P _ => hlocal P)
    _ = _ := hprod
    _ ≤ _ := hbound Z hZ F hF hcut (primeValues (S ∩ H)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact ⟨Q.property,hH Q (Finset.mem_inter.mp hQ).2⟩)

theorem reflected_weight_identity (S H : Finset PrimeIdeal) (d : Id × Id)
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    idealWeight S (fun P => atPrime H P.val) (1/2) (1/2) d*
      ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ) =
        idealWeight S (fun P => atPrime H P.val) (2/3) (1/3) d := by
  have hx : (0 : ℝ) < Ideal.absNorm d.1 := zero_lt_one.trans_le (ideal_norm_one_le hd.1)
  have hy : (0 : ℝ) < Ideal.absNorm d.2 := zero_lt_one.trans_le (ideal_norm_one_le hd.2)
  have hh : normWeight (1/2) d.1*normWeight (1/2) d.2*
      ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ) =
        normWeight (2/3) d.1*normWeight (1/3) d.2 :=
    KernelReflectedMass.central_ratio _ _ hx hy
  unfold idealWeight
  calc
    _ = |(KernelAllocationIdentity.kernelOn S (fun P => atPrime H P.val) d.1 d.2 : ℝ)| *
        (normWeight (1/2) d.1*normWeight (1/2) d.2*
          ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ)) := by ring
    _ = _ := by rw [hh]; ring

/-- The sixth-root length-ratio cost is included before summing the corrections. -/
theorem fixed_support_reflected_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B →
      ∀ (S H : Finset PrimeIdeal), (∀ P ∈ S, Supported P.val) →
      (∀ P ∈ H, P.val ∣ F) →
      ∀ D : Finset (Id × Id), (∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ d ∈ D, idealWeight S (fun P => atPrime H P.val) (1/2) (1/2) d*
        (1+((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ))) ≤ C*Z^ε := by
  obtain ⟨C,hC,hm⟩ := fixed_support_ideal_mass B ε hB hε
  refine ⟨2*C,by positivity,?_⟩
  intro Z hZ F hF hcut S H hS hH D hd hs
  have hc := hm Z hZ F hF hcut S H hS hH (1/2) (1/2) (by norm_num) (by norm_num) D hd hs
  have hr := hm Z hZ F hF hcut S H hS hH (2/3) (1/3) (by norm_num) (by norm_num) D hd hs
  calc
    _ = (∑ d ∈ D, idealWeight S (fun P => atPrime H P.val) (1/2) (1/2) d)+
        ∑ d ∈ D, idealWeight S (fun P => atPrime H P.val) (2/3) (1/3) d := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hdd
      rw [mul_add,mul_one,reflected_weight_identity S H d (hd d hdd)]
    _ ≤ C*Z^ε+C*Z^ε := add_le_add hc hr
    _ = _ := by ring

end
end Candidate.SilPrior.FourthPower.KernelPunctureMass
