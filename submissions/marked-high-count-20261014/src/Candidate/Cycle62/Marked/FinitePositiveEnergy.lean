import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set
open HeckeFamily
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentPositiveSummability
open CenteredMomentPrimeSlot
open CenteredMomentCommonMaskExpansion CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentHeckeTwist CenteredMomentDetectorDictionary
open HeckeRowClosure HeckeDyadic
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

/-- The actual finite row family embeds into the nonnegative natural-state
energy. This keeps the slot coefficients, profiles, mask, and common height
literal rather than replacing them by an abstract moment proposition. -/
theorem finite_positive_energy {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rows : Finset O) (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁⊆Iic b₁) (hs₂ : Function.support W₂⊆Iic b₂)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (pools : Slot→Finset (Ideal O)) (coeff : Slot→Ideal O→ℂ) (P : Slot→ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hkeep : ∀u∈rows,keep u) (hΦ : ∀x,0≤(Φ x).re)
    (hone : ∀u∈rows,Φ (‖eisEmbedding u‖^2/K)=1) :
    (∑u∈rows,‖positiveSlotRow η m A u W₁ W₂ pools coeff P t X₁ X₂‖^2)≤
      energy η m A t W₁ W₂ pools coeff P X₁ X₂ keep Φ K := by
  let normFactor : ℂ := (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
  obtain ⟨B,hB⟩ := product_bounded η m A t normFactor W₁ W₂ b₁ b₂ X₁ X₂
    hs₁ hs₂ hX₁ hX₂ pools coeff
  have hsum := bounded_radial_summable
    (fun u=>positiveSlotRow η m A u W₁ W₂ pools coeff P t X₁ X₂) B hB keep Φ K hK
  have hn (u : O) : 0≤(if keep u then
      ‖positiveSlotRow η m A u W₁ W₂ pools coeff P t X₁ X₂‖^2*
        (Φ (‖eisEmbedding u‖^2/K)).re else 0) := by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  have he := hsum.sum_le_tsum rows (fun u _=>hn u)
  calc
    _ = ∑u∈rows,(if keep u then
        ‖positiveSlotRow η m A u W₁ W₂ pools coeff P t X₁ X₂‖^2*
          (Φ (‖eisEmbedding u‖^2/K)).re else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [if_pos (hkeep u hu),hone u hu,Complex.one_re,mul_one]
    _ ≤ _ := he

/-- The literal natural slot is the source slot whenever their row
presentations agree. Arbitrary arithmetic coefficient factors are preserved. -/
theorem naturalSlot_of_row (η χ : Character) (m A u : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*u) n)
    (pool : Finset (Ideal O)) (coeff : Ideal O→ℂ) (P : ℝ) :
    naturalSlot χ pool coeff P=normalizedSlot η m A u pool coeff 0 P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hc := idealCoeff_eq_row η χ m 1 (A*u) hrow I
  simp only [one_pow,mul_one] at hc
  rw [hc]
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  ring


end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.finite_positive_energy
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.naturalSlot_of_row
