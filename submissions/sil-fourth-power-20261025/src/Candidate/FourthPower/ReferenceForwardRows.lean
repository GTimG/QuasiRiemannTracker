/- Copyright (c) 2026 Sil. Apache-2.0.
Literal forward restricted family with frequency profiles. The resulting
scalars, shortened polynomials, live factor and frozen assignment pool are
exactly those used by the analytic reference, with no absolute-value rewrite.
-/
import Candidate.FourthPower.ReferencePrimeEnclosure
import Candidate.FourthPower.ReferenceNaturalMarkedFactor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.ReferenceForwardRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferencePrimeEnclosure
open KernelRowExpansion KernelRowProfiles KernelRowPools KernelPhysicalScalars
open KernelMarkedRows KernelAssignmentReindex KernelNaturalSlots
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

def validFrozen (T : Finset α) (S : Finset PrimeIdeal) (pool : α → Finset Id) : Finset (T → S) :=
  Finset.univ.filter (fun t => Function.Injective t ∧ ∀ i : T, (t i).val.val ∈ pool i.val)

theorem scalar_zero_of_invalid (χ : Character) (T : Finset α) (S : Finset PrimeIdeal)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (t : T → S) (e : Id × Id)
    (ht : ¬∀ i : T, (t i).val.val ∈ pool i.val) :
    scalar χ S (ordinarySeriesFor false) (markedSeriesFor false)
      (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t e = 0 := by
  obtain ⟨i,hi⟩ := not_forall.mp ht
  have hz : (∏ j : T, slotTerm χ (pool j.val) (β j.val) (P j.val) (t j).val.val) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [slotTerm,hi])
  unfold scalar
  rw [hz,mul_zero]

theorem remaining_constant (T : Finset α) (S : Finset PrimeIdeal) (a : α → S → ℂ)
    (t : T → S) (c : ℂ) :
    remainingSum T a t (fun _ => c) = c*remainingSum T a t (fun _ => 1) := by
  simpa only [mul_one] using remainingSum_mul T a t c (fun _ => 1)

theorem forward_expansion (S : Finset PrimeIdeal)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (Wshort Wlong : ℝ → ℂ) (b X₁ X₂ t₁ t₂ : ℝ)
    (hb : 0 ≤ b) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support Wshort ⊆ Set.Iic b) (hW₂ : Function.support Wlong ⊆ Set.Iic b)
    (H : (T : Finset α) → (T → S) → Factor)
    (hH : ∀ T t χ, remainingSum T (naturalCoefficients χ S pool β P) t (fun _ => 1) = (H T t).value χ)
    (χ : Character) (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
      primeSupport I ⊆ primeValues S) :
    weightedSum (naturalCoefficients χ S pool β P)
      (fun slot => normalizedRow χ (supportedRectangle S b X₁ X₂)
        (sourceValue false S slot) (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) X₁ X₂) =
      ∑ T : Finset α, ∑ t ∈ validFrozen T S pool, ∑ e ∈ divisorPool (supportedRectangle S b X₁ X₂),
        scalar χ S (ordinarySeriesFor false) (markedSeriesFor false)
          (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t e *
          (HeckeDyadic.polynomial χ false Wlong (X₂/Ideal.absNorm e.2) 0 (2*Real.pi*t₂)*
            HeckeDyadic.polynomial χ false Wshort (X₁/Ideal.absNorm e.1) 0 (2*Real.pi*t₁)*
              (H T t).value χ) := by
  rw [natural_rectangle_expansion false S χ pool β P _ _ b X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T hT
  unfold validFrozen
  rw [Finset.sum_filter]
  apply Finset.sum_congr (by ext; simp)
  intro t ht
  by_cases hinj : Function.Injective t
  · by_cases hpool : ∀ i : T, (t i).val.val ∈ pool i.val
    · rw [ite_eq_left hinj,ite_eq_left ⟨hinj,hpool⟩]
      apply Finset.sum_congr rfl
      intro e he
      have he0 := divisor_supported he
      have h₁ := shortened_positive_le hX₁ he0.1
      have h₂ := shortened_positive_le hX₂ he0.2.1
      have hrow := enclosed_phase_pair χ S Wshort Wlong b
        (X₁/Ideal.absNorm e.1) (X₂/Ideal.absNorm e.2) t₁ t₂ h₁.1 h₂.1 hW₁ hW₂ hχ (by
          intro I hI hlen
          apply henclose I hI
          exact hlen.elim
            (fun h => Or.inl (h.trans (mul_le_mul_of_nonneg_left h₁.2 hb)))
            (fun h => Or.inr (h.trans (mul_le_mul_of_nonneg_left h₂.2 hb))))
      simp only [childValue,Bool.false_eq_true,ite_false]
      rw [remaining_constant,hH T t χ,hrow]
      ring
    · rw [ite_eq_left hinj,ite_eq_right (by tauto : ¬(Function.Injective t ∧
        ∀ i : T, (t i).val.val ∈ pool i.val))]
      apply Finset.sum_eq_zero
      intro e he
      rw [scalar_zero_of_invalid χ T S pool β P t e hpool,zero_mul]
  · simp only [hinj,false_and,ite_false]

end
end Candidate.FourthPower.ReferenceForwardRows
