/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussFreeze

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
open CenteredMomentSourceRectangle CenteredMomentRectangle
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Identity at every ordinary coefficient, with ramified zeros retained.
The native residual restriction is exactly an H8 supplying-prime allocation. -/
lemma canonicalPairCoefficient_eq_physical (D : FixedCubeDatum) (M K : Id)
    (hM : M≠0) (hK : K≠0) (hMK : M∣K) (I J : Id) :
    canonicalPairCoefficient D.row.χ K I J=
      if PairAllowed (fixedCubeBad D D (residualSuppliers M∪residualHoles K))
        (supplyingResidualPairs D.row D.row (residualSuppliers M) (residualHoles K) (residualHoles K)) I J
      then D.actualCoefficient I*D.actualCoefficient J else 0 := by
  rw [←D.row_spec.2.2.2 I,←D.row_spec.2.2.2 J]
  by_cases hi : idealCoeff D.row.χ I=0
  · simp [canonicalPairCoefficient,hi]
  by_cases hj : idealCoeff D.row.χ J=0
  · simp [canonicalPairCoefficient,hj]
  have hI : I≠0 := by intro h; exact hi (h ▸ map_zero (idealCoeff D.row.χ))
  have hJ : J≠0 := by intro h; exact hj (h ▸ map_zero (idealCoeff D.row.χ))
  have hcI : IsCoprime I D.row.χ.modulus := by
    by_contra h
    rw [D.row.hind I,if_neg h] at hi
    exact hi rfl
  have hcJ : IsCoprime J D.row.χ.modulus := by
    by_contra h
    rw [D.row.hind J,if_neg h] at hj
    exact hj rfl
  rw [pairAllowed_native_mask D M K I J hI hJ hM hK hMK hcI hcJ]
  unfold canonicalPairCoefficient
  split_ifs <;> rfl

lemma finite_physical_arm (A B : Finset Id) (f : Id→Id→ℂ) (W₁ W₂ : ℝ→ℂ)
    (x y : ℝ)
    (h₁ : ∀I,W₁ ((Ideal.absNorm I : ℝ)/x)≠0→I∈A)
    (h₂ : ∀J,W₂ ((Ideal.absNorm J : ℝ)/y)≠0→J∈B) :
    (∑I : A,∑J : B,f I J*W₁ ((Ideal.absNorm I.val : ℝ)/x)*W₂ ((Ideal.absNorm J.val : ℝ)/y))=
      ∑'p : Id×Id,physicalPairTerm f W₁ W₂ x y p := by
  calc
    _ = ∑I∈A,∑J∈B,f I J*W₁ ((Ideal.absNorm I : ℝ)/x)*W₂ ((Ideal.absNorm J : ℝ)/y) := by
      exact (Finset.sum_coe_sort A (fun I=>∑J:B,f I J*W₁ ((Ideal.absNorm I : ℝ)/x)*W₂ ((Ideal.absNorm J.val : ℝ)/y))).trans
        (Finset.sum_congr rfl (fun I _=>Finset.sum_coe_sort B (fun J=>f I J*W₁ ((Ideal.absNorm I : ℝ)/x)*W₂ ((Ideal.absNorm J : ℝ)/y))))
    _ = ∑p∈A.product B,physicalPairTerm f W₁ W₂ x y p := by
      exact (Finset.sum_product A B (physicalPairTerm f W₁ W₂ x y)).symm
    _ = _ := by
      symm
      apply tsum_eq_sum
      intro p hp
      by_cases hW₁ : W₁ ((Ideal.absNorm p.1 : ℝ)/x)=0
      · simp [physicalPairTerm,hW₁]
      by_cases hW₂ : W₂ ((Ideal.absNorm p.2 : ℝ)/y)=0
      · simp [physicalPairTerm,hW₂]
      exact False.elim (hp (Finset.mem_product.mpr ⟨h₁ _ hW₁,h₂ _ hW₂⟩))

#print axioms finite_physical_arm
#print axioms canonicalPairCoefficient_eq_physical
end
end QRH.Cycle092.FixedCubeGauss
