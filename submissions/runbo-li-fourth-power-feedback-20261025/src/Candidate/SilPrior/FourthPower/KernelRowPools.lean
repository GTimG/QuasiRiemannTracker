/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Exact residual rectangles with a fixed prime enclosure. The finite-fiber
argument follows PR69 Restoration/HoleFibers, retaining our fifth-free
restriction separately. The baseline ideal balls are reused unchanged.
-/
import Candidate.SilPrior.FourthPower.KernelRowProfiles
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.KernelRowPools
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentSourceMass
open UniqueFactorizationMonoid
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelRowExpansion KernelRowProfiles
local notation "Id" => Ideal ActualEisensteinCubic.O

def rectangle (b X₁ X₂ : ℝ) : Finset IdealPair :=
  idealBall (b*X₁) ×ˢ idealBall (b*X₂)

theorem rectangle_nonzero {b X₁ X₂ : ℝ} {n : IdealPair}
    (hn : n ∈ rectangle b X₁ X₂) : n.1 ≠ 0 ∧ n.2 ≠ 0 := by
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hn
  exact ⟨((mem_idealBall _ _).mp hi).1,((mem_idealBall _ _).mp hj).1⟩

theorem rectangle_multiply {b X₁ X₂ : ℝ} {d a : IdealPair}
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    multiplyPair d a ∈ rectangle b X₁ X₂ ↔
      a ∈ rectangle b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  have hi : 0 < (Ideal.absNorm d.1 : ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hd.1)
  have hj : 0 < (Ideal.absNorm d.2 : ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hd.2)
  simp only [rectangle,Finset.mem_product,mem_idealBall,multiplyPair,
    mul_ne_zero_iff,map_mul,Nat.cast_mul]
  have h₁ (x : ℝ) : (Ideal.absNorm d.1 : ℝ)*x ≤ b*X₁ ↔
      x ≤ b*(X₁/Ideal.absNorm d.1) := by
    rw [show b*(X₁/(Ideal.absNorm d.1 : ℝ))=(b*X₁)/Ideal.absNorm d.1 by ring,
      le_div_iff₀ hi,mul_comm x]
  have h₂ (x : ℝ) : (Ideal.absNorm d.2 : ℝ)*x ≤ b*X₂ ↔
      x ≤ b*(X₂/Ideal.absNorm d.2) := by
    rw [show b*(X₂/(Ideal.absNorm d.2 : ℝ))=(b*X₂)/Ideal.absNorm d.2 by ring,
      le_div_iff₀ hj,mul_comm x]
  rw [h₁,h₂]
  tauto

theorem pairSupport_multiply {d a : IdealPair}
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (ha : a.1 ≠ 0 ∧ a.2 ≠ 0) :
    pairSupport (multiplyPair d a).1 (multiplyPair d a).2 =
      pairSupport d.1 d.2 ∪ pairSupport a.1 a.2 := by
  have hp {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) :
      primeSupport (I*J)=primeSupport I ∪ primeSupport J := by
    simp only [primeSupport,IdealMobiusDivisorSum.primeSupport,
      normalizedFactors_mul hI hJ,Multiset.toFinset_add]
  simp only [pairSupport,multiplyPair,hp hd.1 ha.1,hp hd.2 ha.2]
  ext P
  simp only [Finset.mem_union]
  tauto

def supportedRectangle (S : Finset PrimeIdeal) (b X₁ X₂ : ℝ) : Finset IdealPair :=
  (rectangle b X₁ X₂).filter (fun n => pairSupport n.1 n.2 ⊆ primeValues S)

theorem supportedRectangle_nonzero {S : Finset PrimeIdeal} {b X₁ X₂ : ℝ} {n : IdealPair}
    (hn : n ∈ supportedRectangle S b X₁ X₂) : n.1 ≠ 0 ∧ n.2 ≠ 0 :=
  rectangle_nonzero (Finset.mem_filter.mp hn).1

theorem divisor_supported {S : Finset PrimeIdeal} {b X₁ X₂ : ℝ} {d : IdealPair}
    (hd : d ∈ divisorPool (supportedRectangle S b X₁ X₂)) :
    d.1 ≠ 0 ∧ d.2 ≠ 0 ∧ pairSupport d.1 d.2 ⊆ primeValues S := by
  have hdz := divisorPool_nonzero _ (fun _ h => supportedRectangle_nonzero h) hd
  obtain ⟨p,hp,hpd⟩ := Finset.mem_image.mp hd
  obtain ⟨n,hn,hpn⟩ := Finset.mem_biUnion.mp hp
  have he := expandedAt_reconstruct (supportedRectangle_nonzero hn) hpn
  have hi : d.1 ∣ n.1 := by rw [← he,← hpd]; exact dvd_mul_right _ _
  have hj : d.2 ∣ n.2 := by rw [← he,← hpd]; exact dvd_mul_right _ _
  refine ⟨hdz.1,hdz.2,?_⟩
  exact (Finset.union_subset_union
    (primeSupport_subset_of_dvd hdz.1 (supportedRectangle_nonzero hn).1 hi)
    (primeSupport_subset_of_dvd hdz.2 (supportedRectangle_nonzero hn).2 hj)).trans
    (Finset.mem_filter.mp hn).2

theorem cofactor_multiply (d a : IdealPair) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    cofactorPair (multiplyPair d a).1 (multiplyPair d a).2 d = a := by
  apply Prod.ext
  · apply mul_left_cancel₀ hd.1
    exact idealCofactor_mul (dvd_mul_right d.1 a.1)
  · apply mul_left_cancel₀ hd.2
    exact idealCofactor_mul (dvd_mul_right d.2 a.2)

theorem residual_mem_iff (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0) {d a : IdealPair}
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    a ∈ residualPool D d ↔ multiplyPair d a ∈ D := by
  constructor
  · intro ha
    obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp ha
    obtain ⟨hp,hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨n,hn,hpn⟩ := Finset.mem_biUnion.mp hp
    have he := expandedAt_reconstruct (hnz n hn) hpn
    rw [hpd,hpa] at he
    exact he.symm ▸ hn
  · intro hn
    have hnz' := hnz (multiplyPair d a) hn
    have hp : (d,a) ∈ expandedPairs D := by
      apply Finset.mem_biUnion.mpr
      refine ⟨multiplyPair d a,hn,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨d,Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
      · exact (mem_idealDivisors hnz'.1).mpr (dvd_mul_right _ _)
      · exact (mem_idealDivisors hnz'.2).mpr (dvd_mul_right _ _)
      · rw [cofactor_multiply d a hd]
    exact Finset.mem_image.mpr ⟨(d,a),Finset.mem_filter.mpr ⟨hp,rfl⟩,rfl⟩

/-- The residual pool is the full shorter supported rectangle. There is no
extra moving subset in the child and no new puncture at an extracted prime. -/
theorem residual_rectangle {S : Finset PrimeIdeal} {b X₁ X₂ : ℝ} {d : IdealPair}
    (hd : d ∈ divisorPool (supportedRectangle S b X₁ X₂)) :
    residualPool (supportedRectangle S b X₁ X₂) d =
      supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  have hdall := divisor_supported hd
  have hdz : d.1 ≠ 0 ∧ d.2 ≠ 0 := ⟨hdall.1,hdall.2.1⟩
  ext a
  rw [residual_mem_iff _ (fun _ h => supportedRectangle_nonzero h) hdz]
  constructor
  · intro hn
    obtain ⟨hr,hs⟩ := Finset.mem_filter.mp hn
    have har := (rectangle_multiply hdz).mp hr
    apply Finset.mem_filter.mpr
    refine ⟨har,?_⟩
    rw [pairSupport_multiply hdz (rectangle_nonzero har)] at hs
    exact Finset.Subset.trans Finset.subset_union_right hs
  · intro ha
    obtain ⟨har,has⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨(rectangle_multiply hdz).mpr har,?_⟩
    rw [pairSupport_multiply hdz (rectangle_nonzero har)]
    exact Finset.union_subset hdall.2.2 has

/-- Finite truncation of the actual baseline polynomial, using only support
of the common profile. The full character and its natural zeros are retained. -/
theorem natural_polynomial_finite (χ : Character) (W : ℝ → ℂ) (b X : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic b) :
    HeckeDyadic.polynomial χ false W X 0 0 =
      (Real.sqrt X : ℂ)⁻¹ * ∑ I ∈ idealBall (b*X),
        idealCoeff χ I*W ((Ideal.absNorm I : ℝ)/X) := by
  rw [CenteredMomentComparisonReflection.polynomial_plain χ W X hX]
  congr 1
  let f : Id → ℂ := fun I => idealCoeff χ I*W ((Ideal.absNorm I : ℝ)/X)
  have hf : Function.support f ⊆ {I : Id | I ≠ 0} := by
    intro I hi hz
    subst I
    exact hi (by dsimp only [f]; rw [map_zero,zero_mul])
  change (∑' I : {I : Id // I ≠ 0}, f I.val) = _
  apply (tsum_subtype_eq_of_support_subset hf).trans
  apply tsum_eq_sum
  intro I hi
  by_cases hz : I=0
  · subst I
    dsimp only [f]
    rw [map_zero,zero_mul]
  · have hw : W ((Ideal.absNorm I : ℝ)/X)=0 := by
      by_contra h
      exact hi ((mem_idealBall _ _).mpr ⟨hz,(div_le_iff₀ hX).mp (hW h)⟩)
    simp [f,hw]

theorem natural_pair_row (χ : Character) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b) :
    normalizedRow χ (rectangle b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ =
      HeckeDyadic.polynomial χ false W₁ X₁ 0 0 *
        HeckeDyadic.polynomial χ false W₂ X₂ 0 0 := by
  rw [natural_polynomial_finite χ W₁ b X₁ hX₁ hW₁,
    natural_polynomial_finite χ W₂ b X₂ hX₂ hW₂]
  unfold normalizedRow
  rw [Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  simp only [rectangle,Finset.sum_product,pairCharacter,map_mul,pairProfile,one_mul]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hi
  apply Finset.sum_congr rfl
  intro J hj
  ring

variable {α : Type*} [Fintype α]

theorem inverse_full_rectangle (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (χ : Character) (W₁ W₂ : ℝ → ℂ)
    (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ =
      ∑ T : Finset α, ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
        extractedScalar χ
          (fun e => (kernelOn S (fun P => inverseFactor (frozen S slot T P)) e.1 e.2 : ℂ)) d *
        normalizedRow χ
          (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
          (restrictedValue S (frozen S slot Tᶜ)) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [inverse_profile_row S slot hinj _ (fun _ h => supportedRectangle_nonzero h)
    (fun _ h => (Finset.mem_filter.mp h).2) χ W₁ W₂ X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro d hd
  rw [residual_rectangle hd]

theorem forward_full_rectangle (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (χ : Character) (W₁ W₂ : ℝ → ℂ)
    (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ (supportedRectangle S b X₁ X₂)
      (restrictedValue S (marked S slot)) W₁ W₂ X₁ X₂ =
      ∑ T : Finset α, ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
        extractedScalar χ
          (fun e => (kernelOn S (fun P => forwardFactor (frozen S slot T P)) e.1 e.2 : ℂ)) d *
        normalizedRow χ
          (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
          (fun _ => 1) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [forward_profile_row S slot hinj _ (fun _ h => supportedRectangle_nonzero h)
    (fun _ h => (Finset.mem_filter.mp h).2) χ W₁ W₂ X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro d hd
  rw [residual_rectangle hd]

end
end Candidate.SilPrior.FourthPower.KernelRowPools
