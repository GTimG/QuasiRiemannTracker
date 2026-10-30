/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalFinalAssembly
import Submissions.arvi_selected_leaf.JointDetector.NaturalNearPackets
import Submissions.arvi_selected_leaf.JointDetector.NaturalOwnFactorBounds
import Submissions.arvi_selected_leaf.JointDetector.NaturalPunctureBudget
import Submissions.arvi_selected_leaf.JointDetector.NaturalRoundedBudget

/-! The actual finite shared-table norm consumer. Own masks are applied
to their own original vectors before the bilinear estimate; no arbitrary
bounded two-pivot mask is admitted. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss CenteredExceptionalCount IdealMobiusDivisorSum
open NaturalSharedTables NaturalPairPackets NaturalTupleIdentity NaturalNearPackets
local notation "O" => ActualEisensteinCubic.O

theorem actualSectorForm_eq_plain (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j)) (g : SharedTable) (α β : ColourTuple → ℂ)
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (E : Finset (SourceMaskIndex F))
    (k : Oˣ × ℕ × ℕ) (S : Finset (Ideal O)) :
    actualSectorForm F hF g α β W L E k S=
      ∑ r ∈ residualFibre F g,α (recoverLeft g r.1)*β (recoverRight g r.2)*
        ∑ I ∈ S,NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2)
          W L E (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
  unfold actualSectorForm
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_coe_sort S (fun I => α (recoverLeft g r.1)*β (recoverRight g r.2)*
    NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2)
      W L E (BadFrequencySectors.keyFactor k*primaryGenerator I)),Finset.mul_sum]

theorem tableArrayEnergy_mask_le (left : Bool) (F : Finset ColourTuple) (g : SharedTable)
    (a mask : ColourTuple → ℂ) (hm : ∀ c,‖mask c‖ ≤ 1) :
    tableArrayEnergy left F g (fun c => a c*mask c) ≤ tableArrayEnergy left F g a := by
  unfold tableArrayEnergy
  apply Finset.sum_le_sum
  intro b hb
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hm _)

theorem tableArrayEnergy_star (left : Bool) (F : Finset ColourTuple) (g : SharedTable)
    (a : ColourTuple → ℂ) :
    tableArrayEnergy left F g (fun c => star (a c))=tableArrayEnergy left F g a := by
  simp only [tableArrayEnergy,norm_star]

/-- The actual diagonal selector costs two legitimate independent-vector
estimates. Its exceptional unit masks are expressed on their own original
rows, and their masses are contractive. -/
theorem tableSectorPacket_norm_of_bilinear (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0)
    (a : ColourTuple → ℂ) (L H K : ℝ) (hK : 0 ≤ K)
    (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ)
    (j : Fin (columnDyadicLength H+1))
    (hbound : ∀ α β : ColourTuple → ℂ,
      ‖actualSectorForm F hF g α β QuadraticInitialBound.sieveCutoff L E k
        (NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j)‖ ≤
        K*Real.sqrt (tableArrayEnergy true F g α)*Real.sqrt (tableArrayEnergy false F g β)) :
    ‖tableSectorPacket F hF a L H g E k j‖ ≤
      2*K*Real.sqrt (tableArrayEnergy true F g a)*Real.sqrt (tableArrayEnergy false F g a) := by
  let S := NaturalFrequencyReindex.sourceDyad (reflectionFrequencies H) H k j
  let f : ColourTuple × ColourTuple → ℂ := fun r =>
    a (recoverLeft g r.1)*star (a (recoverRight g r.2))*
      ∑ I ∈ S,NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2)
        QuadraticInitialBound.sieveCutoff L E (BadFrequencySectors.keyFactor k*primaryGenerator I)
  let B := K*Real.sqrt (tableArrayEnergy true F g a)*Real.sqrt (tableArrayEnergy false F g a)
  have hfull : ‖∑ r ∈ residualFibre F g,f r‖ ≤ B := by
    have hh := hbound a (fun c => star (a c))
    rw [actualSectorForm_eq_plain,tableArrayEnergy_star] at hh
    exact hh
  have hunit : ‖∑ r ∈ residualFibre F g,
      NaturalDiagonalMask.unitMask r.1*NaturalDiagonalMask.unitMask r.2*f r‖ ≤ B := by
    let α := fun c => a c*leftOriginalUnitMask g c
    let β := fun c => star (a c)*rightOriginalUnitMask g c
    have hh := hbound α β
    have hα : tableArrayEnergy true F g α ≤ tableArrayEnergy true F g a :=
      tableArrayEnergy_mask_le true F g a _ (leftOriginalUnitMask_norm g)
    have hβ : tableArrayEnergy false F g β ≤ tableArrayEnergy false F g a := by
      apply (tableArrayEnergy_mask_le false F g (fun c => star (a c)) _
        (rightOriginalUnitMask_norm g)).trans_eq
      exact tableArrayEnergy_star false F g a
    have hmass : K*Real.sqrt (tableArrayEnergy true F g α)*
        Real.sqrt (tableArrayEnergy false F g β) ≤ B :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hα) hK)
        (Real.sqrt_le_sqrt hβ) (Real.sqrt_nonneg _) (by positivity)
    apply (le_of_eq ?_).trans (hh.trans hmass)
    congr 1
    rw [actualSectorForm_eq_plain]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only [α,β,f]
    rw [leftOriginalUnitMask_recover g hgn,rightOriginalUnitMask_recover g hgn]
    ring
  have hh := NaturalDiagonalMask.sum_offdiagonal_norm_le F hF hpF g (residualFibre F g)
    (Finset.Subset.refl _) f B hfull hunit
  simpa only [tableSectorPacket,S,f,B,mul_assoc] using hh

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.tableSectorPacket_norm_of_bilinear
