/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.IdealMass
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.LocalMass
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.ForwardMass

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal

def allPrimeSupport (D : Finset (Ideal O × Ideal O)) : Finset (Ideal O) :=
  D.biUnion (fun d => pairSupport d.1 d.2)

theorem allPrimeSupport_prime {D : Finset (Ideal O × Ideal O)} {P : Ideal O}
    (hP : P ∈ allPrimeSupport D) : Prime P := by
  obtain ⟨d,hd,hP⟩ := Finset.mem_biUnion.mp hP
  rcases Finset.mem_union.mp hP with hi|hj
  · exact primeSupport_prime hi
  · exact primeSupport_prime hj

def primeClosure (D : Finset (Ideal O × Ideal O)) : Finset PrimeIdeal :=
  (allPrimeSupport D).attach.image (fun P => ⟨P.val,allPrimeSupport_prime P.property⟩)

theorem primeValues_primeClosure (D : Finset (Ideal O × Ideal O)) :
    primeValues (primeClosure D) = allPrimeSupport D := by
  classical
  ext P
  simp [primeValues,primeClosure]
  exact fun h => allPrimeSupport_prime h

def GoodPair (d : Ideal O × Ideal O) : Prop :=
  d.1 ≠ 0 ∧ d.2 ≠ 0 ∧ ∀ P ∈ pairSupport d.1 d.2, 16 ≤ Ideal.absNorm P

theorem prime_z_bound (P : PrimeIdeal) (hP : 16 ≤ Ideal.absNorm P.val)
    (σ : ℝ) (hσ : 1/2 < σ) : (Ideal.absNorm P.val : ℝ)^(-σ) ≤ 1/4 := by
  let x : ℝ := Ideal.absNorm P.val
  have hx : 16 ≤ x := by dsimp [x]; exact_mod_cast hP
  have hx0 : 0 ≤ x := by linarith
  have hz0 : 0 ≤ x^(-σ) := Real.rpow_nonneg hx0 _
  have hsq : (x^(-σ))^2 ≤ (1:ℝ)/16 := by
    calc
      (x^(-σ))^2 = x^(-2*σ) := by rw [← Real.rpow_mul_natCast hx0]; congr 1; ring
      _ ≤ x^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ (16:ℝ)⁻¹ := inv_anti₀ (by norm_num) hx
      _ = 1/16 := by norm_num
  nlinarith

theorem primeWeight_eq_z_squared (P : PrimeIdeal) (σ : ℝ) :
    primeWeight σ P = ((Ideal.absNorm P.val : ℝ)^(-σ))^2 := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  unfold primeWeight
  congr 1
  ring

theorem inverse_good_finite_mass (σ : ℝ) (hσ : 1/2 < σ)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d) :
    ∑ d ∈ D, idealPairWeight inverseCoeff σ d ≤ eulerBound 432 σ := by
  apply finite_ideal_mass_of_local_bound inverseCoeff inverseCoeff_zero σ 432 hσ (by norm_num)
    D (primeClosure D)
  · intro d hd
    exact ⟨(hD d hd).1,(hD d hd).2.1⟩
  · intro d hd
    rw [primeValues_primeClosure]
    exact Finset.subset_biUnion_of_mem (fun d => pairSupport d.1 d.2) hd
  · intro P T
    have hp : 16 ≤ Ideal.absNorm P.val.val := by
      have hm : P.val.val ∈ allPrimeSupport D := by
        rw [← primeValues_primeClosure]
        exact Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩
      obtain ⟨d,hd,hp⟩ := Finset.mem_biUnion.mp hm
      exact (hD d hd).2.2 _ hp
    have hz0 := Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm P.val.val)) (-σ)
    have hz1 := prime_z_bound P.val hp σ hσ
    simpa only [localMassTerm,inverseLocalMass,primeWeight_eq_z_squared] using
      inverseLocalMass_finite T hz0 hz1


theorem forward_good_finite_mass (σ : ℝ) (hσ : 1/2 < σ)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d) :
    ∑ d ∈ D, idealPairWeight forwardCoeff σ d ≤ eulerBound 5 σ := by
  apply finite_ideal_mass_of_local_bound forwardCoeff (by simpa [exponent] using forward_coefficient_at 0 0) σ 5 hσ (by norm_num)
    D (primeClosure D)
  · intro d hd
    exact ⟨(hD d hd).1,(hD d hd).2.1⟩
  · intro d hd
    rw [primeValues_primeClosure]
    exact Finset.subset_biUnion_of_mem (fun d => pairSupport d.1 d.2) hd
  · intro P T
    have hp : 16 ≤ Ideal.absNorm P.val.val := by
      have hm : P.val.val ∈ allPrimeSupport D := by
        rw [← primeValues_primeClosure]
        exact Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩
      obtain ⟨d,hd,hp⟩ := Finset.mem_biUnion.mp hm
      exact (hD d hd).2.2 _ hp
    have hz0 := Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm P.val.val)) (-σ)
    have hz1 : (Ideal.absNorm P.val.val : ℝ)^(-σ) ≤ 1 := (prime_z_bound P.val hp σ hσ).trans (by norm_num)
    simpa only [localMassTerm,forwardLocalMass,primeWeight_eq_z_squared] using
      forwardLocalMass_finite T hz0 hz1


theorem inverse_good_rankin (ε B U : ℝ) (hε : 0 < ε) (hB : 0 < B) (hU : 1 ≤ U)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d)
    (hcut : ∀ d ∈ D, pairNorm d ≤ U^B) :
    ∑ d ∈ D, idealPairWeight inverseCoeff (1/2) d ≤
      eulerBound 432 (1/2+ε/B) * U^ε := by
  have hδ : 0 < ε/B := div_pos hε hB
  have hu0 : 0 < U := by linarith
  have h := rankin_finite_mass inverseCoeff (1/2+ε/B) (U^B)
    (eulerBound 432 (1/2+ε/B)) (by linarith) (Real.rpow_pos_of_pos hu0 _)
    D (fun d hd => ⟨(hD d hd).1,(hD d hd).2.1⟩) hcut
    (inverse_good_finite_mass (1/2+ε/B) (by linarith) D hD)
  have heq : (U^B)^(1/2+ε/B-1/2) = U^ε := by
    rw [← Real.rpow_mul hu0.le]
    congr 1
    field_simp
    ring
  simpa only [heq,mul_comm] using h

theorem forward_good_rankin (ε B U : ℝ) (hε : 0 < ε) (hB : 0 < B) (hU : 1 ≤ U)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d)
    (hcut : ∀ d ∈ D, pairNorm d ≤ U^B) :
    ∑ d ∈ D, idealPairWeight forwardCoeff (1/2) d ≤
      eulerBound 5 (1/2+ε/B) * U^ε := by
  have hδ : 0 < ε/B := div_pos hε hB
  have hu0 : 0 < U := by linarith
  have h := rankin_finite_mass forwardCoeff (1/2+ε/B) (U^B)
    (eulerBound 5 (1/2+ε/B)) (by linarith) (Real.rpow_pos_of_pos hu0 _)
    D (fun d hd => ⟨(hD d hd).1,(hD d hd).2.1⟩) hcut
    (forward_good_finite_mass (1/2+ε/B) (by linarith) D hD)
  have heq : (U^B)^(1/2+ε/B-1/2) = U^ε := by
    rw [← Real.rpow_mul hu0.le]
    congr 1
    field_simp
    ring
  simpa only [heq,mul_comm] using h

theorem inverse_good_mass_0501 : ∃ C : ℝ, 0<C ∧
    ∀ D : Finset (Ideal O × Ideal O), (∀ d ∈ D, GoodPair d) →
      ∑ d ∈ D, idealPairWeight inverseCoeff (501/1000) d ≤ C := by
  exact ⟨eulerBound 432 (501/1000),eulerBound_pos _ _,fun D hD =>
    inverse_good_finite_mass _ (by norm_num) D hD⟩


def kernelAbsoluteMassTerm (σ : ℝ) (d : Ideal O × Ideal O) : ℝ :=
  (|(forwardKernel d.1 d.2 : ℝ)|+|(inverseKernel d.1 d.2 : ℝ)|)/pairNorm d^σ

theorem kernelAbsoluteMassTerm_eq (σ : ℝ) (d : Ideal O × Ideal O) :
    kernelAbsoluteMassTerm σ d = idealPairWeight forwardCoeff σ d + idealPairWeight inverseCoeff σ d := by
  rw [idealPairWeight_eq_pairNorm,idealPairWeight_eq_pairNorm]
  unfold kernelAbsoluteMassTerm forwardKernel inverseKernel forwardCoeff
  rw [Real.rpow_neg (show 0 ≤ pairNorm d by unfold pairNorm; positivity),div_eq_mul_inv,add_mul]

theorem good_absolute_finite_mass (σ : ℝ) (hσ : 1/2 < σ)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d) :
    ∑ d ∈ D, kernelAbsoluteMassTerm σ d ≤ eulerBound 5 σ + eulerBound 432 σ := by
  simp only [kernelAbsoluteMassTerm_eq,Finset.sum_add_distrib]
  exact add_le_add (forward_good_finite_mass σ hσ D hD) (inverse_good_finite_mass σ hσ D hD)

theorem good_absolute_mass_0501 : ∃ C : ℝ, 0<C ∧
    ∀ D : Finset (Ideal O × Ideal O), (∀ d ∈ D, GoodPair d) →
      ∑ d ∈ D, kernelAbsoluteMassTerm (501/1000) d ≤ C := by
  exact ⟨eulerBound 5 (501/1000)+eulerBound 432 (501/1000),
    add_pos (eulerBound_pos _ _) (eulerBound_pos _ _),fun D hD =>
      good_absolute_finite_mass _ (by norm_num) D hD⟩

theorem good_absolute_rankin (ε B U : ℝ) (hε : 0 < ε) (hB : 0 < B) (hU : 1 ≤ U)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d)
    (hcut : ∀ d ∈ D, pairNorm d ≤ U^B) :
    ∑ d ∈ D, (|(forwardKernel d.1 d.2 : ℝ)|+|(inverseKernel d.1 d.2 : ℝ)|)/Real.sqrt (pairNorm d) ≤
      (eulerBound 5 (1/2+ε/B)+eulerBound 432 (1/2+ε/B))*U^ε := by
  simp only [Real.sqrt_eq_rpow]
  change ∑ d ∈ D, kernelAbsoluteMassTerm (1/2) d ≤ _
  simp only [kernelAbsoluteMassTerm_eq,Finset.sum_add_distrib,add_mul]
  exact add_le_add (forward_good_rankin ε B U hε hB hU D hD hcut)
    (inverse_good_rankin ε B U hε hB hU D hD hcut)


theorem good_absolute_rankin_nonnegative (ε B U : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hU : 1 ≤ U)
    (D : Finset (Ideal O × Ideal O)) (hD : ∀ d ∈ D, GoodPair d)
    (hcut : ∀ d ∈ D, pairNorm d ≤ U^B) :
    ∑ d ∈ D, (|(forwardKernel d.1 d.2 : ℝ)|+|(inverseKernel d.1 d.2 : ℝ)|)/Real.sqrt (pairNorm d) ≤
      (eulerBound 5 (1/2+ε/(B+1))+eulerBound 432 (1/2+ε/(B+1)))*U^ε := by
  apply good_absolute_rankin ε (B+1) U hε (by linarith) hU D hD
  intro d hd
  exact (hcut d hd).trans (Real.rpow_le_rpow_of_exponent_le hU (by linarith))

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.inverse_good_finite_mass

#print axioms QRH.Record1252270103KernelMass.good_absolute_rankin
#print axioms QRH.Record1252270103KernelMass.good_absolute_mass_0501
