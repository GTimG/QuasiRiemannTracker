/-
The whole packed row polynomial at a sixth root as one ordinary polynomial in the free core.
-/
import Submissions.arvi_selected_leaf.R1.RootRow

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy CenteredMomentSourceMass
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

/-- The normalized plain sum at the root `g` (length `X`, support radius `b`). -/
def plainPoly (η : Character) (m g : O) (W : ℝ → ℂ) (t X b : ℝ) : OrdPoly :=
  ⟨idealBall (b*X), fun I => (Real.sqrt X : ℂ)⁻¹ *
    (rootCommon η m g t I.val * W ((Ideal.absNorm I.val : ℝ)/X))⟩

/-- The normalized slot at the root `g`. -/
def slotPoly (η : Character) (m g : O) (S : Finset (Ideal O)) (β : Ideal O → ℂ) (t P : ℝ) : OrdPoly :=
  ⟨S, fun I => (Real.sqrt P : ℂ)⁻¹ * β I.val * rootCommon η m g t I.val⟩

theorem plainPoly_eval (η : Character) (m u g : O) (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (plainPoly η m g W t X b).eval u = (Real.sqrt X : ℂ)⁻¹ * rowTwistedSum η m 1 (u * g^6) W t X := by
  rw [rowTwistedSum_root η m u g W t X b hX hs]
  simp only [OrdPoly.eval, plainPoly, ordinaryPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem slotPoly_eval (η : Character) (m u g : O) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (t P : ℝ) :
    (slotPoly η m g S β t P).eval u = normalizedSlot η m 1 (u * g^6) S β t P := by
  rw [normalizedSlot_root]
  rfl

variable {ι : Type*} [Fintype ι]

/-- The whole row polynomial at the root `g`. -/
def rowPoly (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b₁ b₂ : ℝ) : OrdPoly :=
  OrdPoly.prod ([plainPoly η m g W₁ t X₁ b₁, plainPoly η m g W₂ t X₂ b₂] ++
    (Finset.univ.toList.map (fun i => slotPoly η m g (S i) (β i) t (P i))))

/-- **The packed row at a sixth root is the row polynomial evaluated at the core.** -/
theorem positiveSlotRow_root (η : Character) (m u g : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b₁ b₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    positiveSlotRow η m 1 (u * g^6) W₁ W₂ S β P t X₁ X₂ =
      (rowPoly η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂).eval u := by
  rw [rowPoly, OrdPoly.eval_prod, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.map_map,
    Function.comp_def]
  rw [Finset.prod_map_toList]
  simp only [plainPoly_eval η m u g W₁ t X₁ b₁ hX₁ hs₁, plainPoly_eval η m u g W₂ t X₂ b₂ hX₂ hs₂,
    slotPoly_eval]
  unfold positiveSlotRow
  simp only [normalizedSlot]
  have hPpos : 0 ≤ ∏ i, P i := Finset.prod_nonneg (fun i _ => (hP i).le)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hX₁.le, Real.sqrt_prod _ (fun i _ => (hP i).le)]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  ring

end
end QRH.ArviSelectedLeaf.R1
