/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.ConfigurationMass

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103KernelMass
noncomputable section
open scoped BigOperators
open Record1252270103TwoIdeal

def idealPairWeight (f : Exponent → ℤ) (σ : ℝ) (d : Ideal O × Ideal O) : ℝ :=
  |(idealKernel f d.1 d.2 : ℝ)| * normWeight σ d.1 * normWeight σ d.2

def primeValues (S : Finset PrimeIdeal) : Finset (Ideal O) := S.image Subtype.val

def encodePair (S : Finset PrimeIdeal) (d : Ideal O × Ideal O) : S → ℕ×ℕ :=
  fun P => (valuation d.1 P.val.val,valuation d.2 P.val.val)

theorem idealPairWeight_eq_prod (f : Exponent → ℤ) (hf : f 0=1) (σ : ℝ)
    {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) (hS : pairSupport I J ⊆ S) :
    idealPairWeight f σ (I,J) = ∏ P ∈ S,
      |(f (localExponent I J P) : ℝ)| * ((Ideal.absNorm P : ℝ)^(-σ))^(valuation I P+valuation J P) := by
  have hi : primeSupport I ⊆ S := Finset.Subset.trans Finset.subset_union_left hS
  have hj : primeSupport J ⊆ S := Finset.Subset.trans Finset.subset_union_right hS
  unfold idealPairWeight
  dsimp only
  rw [idealKernel_eq_prod f hf hI hJ S hS,normWeight_eq_prod hI S hi σ,
    normWeight_eq_prod hJ S hj σ]
  push_cast
  rw [Finset.abs_prod,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [pow_add,mul_assoc]

theorem idealPairWeight_eq_configuration (f : Exponent → ℤ) (hf : f 0=1) (σ : ℝ)
    {d : Ideal O × Ideal O} (hI : d.1 ≠ 0) (hJ : d.2 ≠ 0)
    (S : Finset PrimeIdeal) (hS : pairSupport d.1 d.2 ⊆ primeValues S) :
    idealPairWeight f σ d = ∏ P : S, localMassTerm f σ P.val (encodePair S d P) := by
  rw [idealPairWeight_eq_prod f hf σ hI hJ (primeValues S) hS]
  unfold primeValues
  rw [Finset.prod_image]
  · exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp) _)
  · intro P hP Q hQ heq
    exact Subtype.val_injective heq

theorem encodePair_injective {S : Finset PrimeIdeal} {d e : Ideal O × Ideal O}
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (he : e.1 ≠ 0 ∧ e.2 ≠ 0)
    (hds : pairSupport d.1 d.2 ⊆ primeValues S)
    (hes : pairSupport e.1 e.2 ⊆ primeValues S)
    (h : encodePair S d = encodePair S e) : d=e := by
  apply Prod.ext
  · apply ideals_eq_of_valuations_on hd.1 he.1 (primeValues S)
      (Finset.Subset.trans Finset.subset_union_left hds)
      (Finset.Subset.trans Finset.subset_union_left hes)
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact congrArg Prod.fst (congrFun h ⟨Q,hQ⟩)
  · apply ideals_eq_of_valuations_on hd.2 he.2 (primeValues S)
      (Finset.Subset.trans Finset.subset_union_right hds)
      (Finset.Subset.trans Finset.subset_union_right hes)
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact congrArg Prod.snd (congrFun h ⟨Q,hQ⟩)


def pairNorm (d : Ideal O × Ideal O) : ℝ := (Ideal.absNorm d.1 : ℝ)*(Ideal.absNorm d.2 : ℝ)

theorem pairNorm_pos {d : Ideal O × Ideal O} (hI : d.1 ≠ 0) (hJ : d.2 ≠ 0) : 0 < pairNorm d := by
  unfold pairNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_iff_ne_zero.mpr (by
    intro h
    first | exact hI (Ideal.absNorm_eq_zero_iff.mp h) | exact hJ (Ideal.absNorm_eq_zero_iff.mp h))

theorem idealPairWeight_eq_pairNorm (f : Exponent → ℤ) (σ : ℝ) (d : Ideal O × Ideal O) :
    idealPairWeight f σ d = |(idealKernel f d.1 d.2 : ℝ)| * pairNorm d ^ (-σ) := by
  unfold idealPairWeight normWeight pairNorm
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),mul_assoc]

theorem rankin_finite_mass (f : Exponent → ℤ) (σ X M : ℝ) (hσ : 1/2 ≤ σ)
    (hX : 0 < X) (D : Finset (Ideal O × Ideal O))
    (hnz : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hcut : ∀ d ∈ D, pairNorm d ≤ X)
    (hmass : ∑ d ∈ D, idealPairWeight f σ d ≤ M) :
    ∑ d ∈ D, idealPairWeight f (1/2) d ≤ X^(σ-1/2)*M := by
  have ht : ∀ d ∈ D, idealPairWeight f (1/2) d ≤ X^(σ-1/2)*idealPairWeight f σ d := by
    intro d hd
    have hp := pairNorm_pos (hnz d hd).1 (hnz d hd).2
    rw [idealPairWeight_eq_pairNorm,idealPairWeight_eq_pairNorm]
    have heq : pairNorm d ^ (-(1/2:ℝ)) = pairNorm d ^ (-σ)*pairNorm d ^ (σ-1/2) := by
      rw [← Real.rpow_add hp]
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ |(idealKernel f d.1 d.2 : ℝ)| * (pairNorm d ^ (-σ)*X^(σ-1/2)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
        exact Real.rpow_le_rpow hp.le (hcut d hd) (by linarith)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ D, X^(σ-1/2)*idealPairWeight f σ d := Finset.sum_le_sum ht
    _ = X^(σ-1/2)*(∑ d ∈ D, idealPairWeight f σ d) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hX.le _)


theorem finite_ideal_mass_product (f : Exponent → ℤ) (hf : f 0=1)
    (σ : ℝ)
    (D : Finset (Ideal O × Ideal O)) (S : Finset PrimeIdeal)
    (hnz : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hsupport : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S)
    : ∑ d ∈ D, idealPairWeight f σ d ≤ ∏ P : S,
      ∑ ij ∈ D.image (fun d => encodePair S d P), localMassTerm f σ P.val ij := by
  classical
  let t : S → Finset (ℕ×ℕ) := fun P => D.image (fun d => encodePair S d P)
  have himage : D.image (encodePair S) ⊆ Fintype.piFinset t := by
    intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    simp only [Fintype.mem_piFinset]
    intro P
    exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hinj : Set.InjOn (encodePair S) (↑D : Set (Ideal O × Ideal O)) := by
    intro d hd e he heq
    exact encodePair_injective (hnz d hd) (hnz e he) (hsupport d hd) (hsupport e he) heq
  calc
    ∑ d ∈ D, idealPairWeight f σ d =
        ∑ a ∈ D.image (encodePair S), ∏ P : S, localMassTerm f σ P.val (a P) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro d hd
      exact idealPairWeight_eq_configuration f hf σ (hnz d hd).1 (hnz d hd).2 S (hsupport d hd)
    _ ≤ ∑ a ∈ Fintype.piFinset t, ∏ P : S, localMassTerm f σ P.val (a P) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro a ha hna
      exact Finset.prod_nonneg (fun P _ => localMassTerm_nonneg f σ P.val (a P))
    _ = _ := (Finset.prod_univ_sum _ _).symm

theorem finite_ideal_mass_of_local_bound (f : Exponent → ℤ) (hf : f 0=1)
    (σ C : ℝ) (hσ : 1/2 < σ) (hC : 0 ≤ C)
    (D : Finset (Ideal O × Ideal O)) (S : Finset PrimeIdeal)
    (hnz : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hsupport : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S)
    (hlocal : ∀ P : S, ∀ T : Finset (ℕ×ℕ),
      ∑ ij ∈ T, localMassTerm f σ P.val ij ≤ 1+C*primeWeight σ P.val) :
    ∑ d ∈ D, idealPairWeight f σ d ≤ eulerBound C σ := by
  classical
  calc
    _ ≤ ∏ P : S, ∑ ij ∈ D.image (fun d => encodePair S d P), localMassTerm f σ P.val ij :=
      finite_ideal_mass_product f hf σ D S hnz hsupport
    _ ≤ ∏ P : S, (1+C*primeWeight σ P.val) := by
      apply Finset.prod_le_prod₀
      · intro P hP
        exact Finset.sum_nonneg (fun ij _ => localMassTerm_nonneg f σ P.val ij)
      · intro P hP
        exact hlocal P _
    _ = ∏ P ∈ S, (1+C*primeWeight σ P) :=
      (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp) (fun P => 1+C*primeWeight σ P)).symm
    _ ≤ eulerBound C σ := finite_euler_bound C σ hC hσ S

end
end QRH.Record1252270103KernelMass
#print axioms QRH.Record1252270103KernelMass.idealPairWeight_eq_configuration
#print axioms QRH.Record1252270103KernelMass.encodePair_injective
