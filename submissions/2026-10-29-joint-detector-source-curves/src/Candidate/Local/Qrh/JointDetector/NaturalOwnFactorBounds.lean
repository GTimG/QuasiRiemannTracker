/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalNearPackets

/-! Contractive actual own factors on projected, possibly nonrectangular
residual families. All family bounds follow from original-pair witnesses.
Radical-dyad restrictions are imposed only on the terms being summed. -/
namespace Qrh.JointDetector.NaturalOwnFactorBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalQuadraticSieve CompletedGauss
open NaturalSelectedNorm NaturalSharedTables NaturalNearPackets
local notation "O" => ActualEisensteinCubic.O

theorem leftOwnFactor_norm_onFamily (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a : ColourTuple) (ha : a ∈ leftFamily F g) (q b : O) :
    ‖leftOwnFactor F hF g a q b‖ ≤ 1 := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨c,d⟩,hp,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hcd,ht⟩ := Finset.mem_filter.mp hp
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  change ‖leftOwnFactor F hF g (leftResidual c d) q b‖ ≤ 1
  rw [← ht]
  exact leftOwnFactor_norm_actual F hF c d hc hd (hpF c hc) (hpF d hd) q b

theorem rightOwnFactor_norm_onFamily (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a : ColourTuple) (ha : a ∈ rightFamily F g) (q b : O) :
    ‖rightOwnFactor F hF g a q b‖ ≤ 1 := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨c,d⟩,hp,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hcd,ht⟩ := Finset.mem_filter.mp hp
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  change ‖rightOwnFactor F hF g (rightResidual c d) q b‖ ≤ 1
  rw [← ht]
  exact rightOwnFactor_norm_actual F hF c d hc hd (hpF c hc) (hpF d hd) q b

theorem radicalWeight_norm_le (D : ℝ) (a : ColourTuple)
    (ha : ∀ j,Admissible (a j)) (hD : 0 ≤ D) (hDa : D ≤ radicalNorm a) :
    ‖radicalWeight D a‖ ≤ 1 := by
  have hrad : 0 < radicalNorm a :=
    CenteredExceptionalCount.norm_pos (TuplePartition.radical_ne_zero a ha)
  simpa only [radicalWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using radical_weight_le_one D (radicalNorm a) hD hrad hDa

theorem leftPacketArray_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (D : ℝ) (u : ElementFibre (leftFamily F g))
    (hD : 0 ≤ D) (hDu : D ≤ radicalNorm (fibreTuple (leftFamily F g) hLF u)) :
    ‖leftPacketArray F hF g hLF α q b D u‖ ≤
      ‖α (recoverLeft g (fibreTuple (leftFamily F g) hLF u))‖ := by
  have hu := fibreTuple_mem (leftFamily F g) hLF u
  have ho := leftOwnFactor_norm_onFamily F hF hpF g _ hu q b
  have hr := radicalWeight_norm_le D _ (hLF _ hu) hD hDu
  unfold leftPacketArray
  dsimp only
  rw [norm_mul,norm_mul]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left ho (norm_nonneg _)) hr
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem rightPacketArray_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (D : ℝ) (u : ElementFibre (rightFamily F g))
    (hD : 0 ≤ D) (hDu : D ≤ radicalNorm (fibreTuple (rightFamily F g) hRF u)) :
    ‖rightPacketArray F hF g hRF α q b D u‖ ≤
      ‖α (recoverRight g (fibreTuple (rightFamily F g) hRF u))‖ := by
  have hu := fibreTuple_mem (rightFamily F g) hRF u
  have ho := rightOwnFactor_norm_onFamily F hF hpF g _ hu q b
  have hr := radicalWeight_norm_le D _ (hRF _ hu) hD hDu
  unfold rightPacketArray
  dsimp only
  rw [norm_mul,norm_mul]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left ho (norm_nonneg _)) hr
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Exact mass before the contractive factors are inserted. -/
theorem left_original_mass (F : Finset ColourTuple) (g : SharedTable)
    (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j)) (α : ColourTuple → ℂ) :
    (∑ u : ElementFibre (leftFamily F g),
      ‖α (recoverLeft g (fibreTuple (leftFamily F g) hLF u))‖^2) =
      ∑ a ∈ leftFamily F g,‖α (recoverLeft g a)‖^2 := by
  change (∑ u : ElementFibre (leftFamily F g),
    ‖(fun a : leftFamily F g => α (recoverLeft g a.val))
      ((tupleElementFibreEquiv (leftFamily F g) hLF).symm u)‖^2)=_
  rw [tupleElementFibre_mass (leftFamily F g) hLF (fun a => α (recoverLeft g a.val))]
  exact Finset.sum_coe_sort (leftFamily F g) (fun a => ‖α (recoverLeft g a)‖^2)

theorem right_original_mass (F : Finset ColourTuple) (g : SharedTable)
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (α : ColourTuple → ℂ) :
    (∑ u : ElementFibre (rightFamily F g),
      ‖α (recoverRight g (fibreTuple (rightFamily F g) hRF u))‖^2) =
      ∑ a ∈ rightFamily F g,‖α (recoverRight g a)‖^2 := by
  change (∑ u : ElementFibre (rightFamily F g),
    ‖(fun a : rightFamily F g => α (recoverRight g a.val))
      ((tupleElementFibreEquiv (rightFamily F g) hRF).symm u)‖^2)=_
  rw [tupleElementFibre_mass (rightFamily F g) hRF (fun a => α (recoverRight g a.val))]
  exact Finset.sum_coe_sort (rightFamily F g) (fun a => ‖α (recoverRight g a)‖^2)

/-- A genuine finite radical dyad may be any subset of the original fibre.
The complementary rows are not assigned a fictitious radical bound. -/
theorem leftPacketArray_subset_mass (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (D : ℝ) (hD : 0 ≤ D)
    (Q : Finset (ElementFibre (leftFamily F g)))
    (hQ : ∀ u ∈ Q,D ≤ radicalNorm (fibreTuple (leftFamily F g) hLF u)) :
    (∑ u ∈ Q,‖leftPacketArray F hF g hLF α q b D u‖^2) ≤
      ∑ a ∈ leftFamily F g,‖α (recoverLeft g a)‖^2 := by
  calc
    _ ≤ ∑ u ∈ Q,‖α (recoverLeft g (fibreTuple (leftFamily F g) hLF u))‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact pow_le_pow_left₀ (norm_nonneg _)
        (leftPacketArray_norm_le F hF hpF g hLF α q b D u hD (hQ u hu)) 2
    _ ≤ ∑ u : ElementFibre (leftFamily F g),
        ‖α (recoverLeft g (fibreTuple (leftFamily F g) hLF u))‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => sq_nonneg _)
    _ = _ := left_original_mass F g hLF α

theorem rightPacketArray_subset_mass (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (D : ℝ) (hD : 0 ≤ D)
    (Q : Finset (ElementFibre (rightFamily F g)))
    (hQ : ∀ u ∈ Q,D ≤ radicalNorm (fibreTuple (rightFamily F g) hRF u)) :
    (∑ u ∈ Q,‖rightPacketArray F hF g hRF α q b D u‖^2) ≤
      ∑ a ∈ rightFamily F g,‖α (recoverRight g a)‖^2 := by
  calc
    _ ≤ ∑ u ∈ Q,‖α (recoverRight g (fibreTuple (rightFamily F g) hRF u))‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact pow_le_pow_left₀ (norm_nonneg _)
        (rightPacketArray_norm_le F hF hpF g hRF α q b D u hD (hQ u hu)) 2
    _ ≤ ∑ u : ElementFibre (rightFamily F g),
        ‖α (recoverRight g (fibreTuple (rightFamily F g) hRF u))‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => sq_nonneg _)
    _ = _ := right_original_mass F g hRF α

end
end Qrh.JointDetector.NaturalOwnFactorBounds

#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.leftOwnFactor_norm_onFamily
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.rightOwnFactor_norm_onFamily
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.radicalWeight_norm_le
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.leftPacketArray_norm_le
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.rightPacketArray_norm_le
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.left_original_mass
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.right_original_mass
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.leftPacketArray_subset_mass
#print axioms Qrh.JointDetector.NaturalOwnFactorBounds.rightPacketArray_subset_mass
